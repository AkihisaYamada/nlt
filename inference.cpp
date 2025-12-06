#include "inference.hpp"
using namespace std;

void cerr_proof_thms( Thy const& thy ) {
	for( auto const& name : { Thy::EXACT, Thy::CONCL, Thy::INTRO, Thy::WEAK, Thy::ELIM } ) {
		cerr << name << ":" << thy.print_thms(name);
	}
}

CTerm dummy( Ctxt const& ctxt ) {
	return ctxt.cterm(DUMMY);
}
Error const Inference::NoGoal = Error("\"no goal to apply\"");
Error const Inference::Unapplicable = Error("\"apply failed\"");

Intro Intro::imp( Thm const& thm, size_t n ) {
	auto child = thm.ctxt().fork();
	auto self = child.ctxt().self();
	auto f = fresh_maker();
	Thm rule = thm.subst(child);
	size_t vars = 0;
	for( size_t i = 0;; i++ ) {
		if( i == n ) return Intro(thm,rule,vars,i);
		auto const& [rule2,vars2] = strip_all(rule,self,f);
		vars += vars2;
		auto imp = rule2.cbinary(IMP);
		assert(imp);
		rule = rule2.discharge(child.ctxt().assume(imp->first));
	}
}

Intro Intro::rule( Thm const& thm ) {
	auto intp = thm.ctxt().fork();
	auto f = fresh_maker();
	auto [conc,vars] = strip_all(thm,intp,f);
	auto ctxt = intp.ctxt();
	size_t conds = 0;
	while( auto imp = conc.cbinary(IMP) ) {
		conc = conc.discharge(ctxt.assume(imp->first));
		conds++;
		conc = strip_all(conc,ctxt.self(),f).first;
	}
	return Intro(thm,conc,vars,conds);
}
Elim Elim::rule( Thm const& thm ) {
	auto child = thm.ctxt().fork();
	Thm body = strip_all(thm,child,fresh_maker()).first;
	auto imp = body.cbinary(IMP);
	if( !imp ) throw Error("\"malformed elimination rule\"")(thm);
	Thm premise = child.ctxt().assume(imp->first);
	body = body.discharge(premise);
	return Elim(thm,premise,body);
}
Intro Elim::instantiate( Subst& m, Thm const& arg, Intp const& intp ) const {
	auto pat_ctxt = _premise.ctxt();
	auto thm_ctxt = _thm.ctxt();
	auto pat2loc = Intp::make(pat_ctxt,thm_ctxt).compose(intp);
	subst_intp(pat2loc,m);
	pat2loc.discharge(arg);
	auto thm = _rule.subst(pat2loc);// ∀thesis. ψθ... ⟹ thesis
	return Intro::rule(thm);
}

void add_forced( Thy& thy, Thm const& thm, bool allow_intro ) {
	auto intro = Intro::rule(thm);
	if( intro.conds() > 0 ) {
		thy.add_thm( allow_intro ? Thy::INTRO : Thy::WEAK, thm, {intro} );
	} else if( intro.vars() > 0 ) {
		thy.add_thm(Thy::CONCL,thm,{intro});
	} else {
		thy.add_thm(Thy::EXACT,thm);
	}
}
void Inference::_apply( std::set<Intro> const& rules, size_t& suc, size_t min, size_t max, bool safe, bool wide ) & {
	for(;;) {
		if( _goals == 0 ) {
			if( suc < min ) throw Error("\"no more goal to apply on\"");
			return;
		}
		if( suc == max ) {
			if( !safe ) throw Error("\"apply limit exceeded\"")(to_string(max));
			return;
		}
		auto child = _thy.branch();
		if( !_apply(rules,child.weaken(goal()),child) ) {
			break;
		}
		suc++;
	}
	if( wide && push() ) {
		_apply(rules,suc,min,max,safe,wide);
		pop();
	}
	if( suc < min ) throw Error("\"apply failed\"");
}
bool Inference::_apply_blast(
	Subst const& matcher,
	Intp const& rule2child,
	size_t& fuel,
	size_t trial,
	Intro const& rule,
	Ctrl const& ctrl
) & {
	// interpret the context where the theorem to apply is proved.
	auto rule_ctxt = rule.thm().ctxt();
	// then interpret the context holding the pattern variables and premises.
	auto pat_intp = Intp::make(rule.conclusion().ctxt(),rule_ctxt).compose(rule2child);
	for(;;) {
		if( auto const& v = pat_intp.fixing() ) {// instantiate pattern variables
			if( auto const& val = matcher.get(*v) ) {
				pat_intp.instantiate(*val);
			} else {
				pat_intp.instantiate(dummy(_thy));
			}
		} else if( auto const& assm = pat_intp.assuming() ) {// discharge assumptions
			Inference thesis = claim_exact(_thy,*assm);
			vector<Intro> elim_res;
			if( !thesis._blast(fuel,trial,ctrl,true,elim_res,0) ) return false;
			pat_intp.discharge(thesis._thm);
		} else {
			break;
		}
	}
	auto claim = rule.subst(pat_intp);
	_thm = _thm.discharge(claim);
	_goals--;
	return true;
}

bool Inference::_apply( Intro const& rule, CTerm const& goal, Thy const& child ) & {
	auto const& m = rule.matches(goal);
	if( !m ) return false;
	// interpret the context where the theorem to apply is proved.
	auto rule2child = child.interpret_ancestor(rule.thm().ctxt());
	_apply2(*m,rule,child,rule2child);
	return true;
}

void Inference::_apply2( Subst const& matcher, Intro const& intro, Thy const& child, Intp const& rule2child ) & {
	// then interpret the context holding the pattern variables and premises.
	auto pat2child = Intp::make(intro.conclusion().ctxt(),intro.thm().ctxt()).compose(rule2child);
	auto ctxt = matcher.ctxt();
	for(;;) {
		if( auto const& v = pat2child.fixing() ) {// instantiate pattern variables
			if( auto const& val = matcher.get(*v) ) {
				pat2child.instantiate(*val);
			} else {
				pat2child.instantiate(dummy(ctxt));
			}
			continue;
		}
		if( auto const& assm = pat2child.assuming() ) {// make assumptions
			pat2child.discharge(ctxt.assume(*assm));
			_goals++;
			continue;
		}
		break;
	}
	_thm = child.weaken(_thm).discharge(intro.conclusion().subst(pat2child)).intro();
	_goals--;
}

struct BlastError : public Error {
	inline static Error const RT = Error("#blast");
	BlastError( Error const& err ) : Error(err) {}
	BlastError( Term const& msg ) : Error(RT(msg)) {}
	BlastError operator()( Term const& msg ) const {
		return BlastError(((Error)*this)(msg));
	}
};

bool Inference::_blast(
	size_t& fuel,
	size_t trial,
	Ctrl const& ctrl,
	bool fail,
	vector<Intro>& elim_res,
	size_t elim_res_ind
) & {
	if( ctrl.log > 1 ) cout << _thy.pretty(goal()) << endl;
	if( _goals == 0 ) {// no goal to blast
		throw BlastError("\"no goal to blast\"");
	}
	if( fuel == 0 ) {
		if( fail ) return false;
		throw BlastError("\"blast limit exceeded\"");
	}
	auto const& imp = _thm.cbinary(IMP);
	assert(imp);
	auto subthy = _thy.branch();
	auto goal = subthy.weaken(imp->first);
	size_t n_elim_res = 0;
	for(;;) {// strip all assumptions
		goal = strip_all(goal,subthy.self());
		auto imp = goal.cbinary(IMP);
		if( !imp ) break;// no more assumption
		auto assm = subthy.assume(imp->first);// make the assumption
		goal = imp->second;
		if( auto const& rew = ctrl.rewrite ) {// rewrite the assumption
			assm = subthy.rewrite(assm,rew->first,rew->second);
		}
		// checks if an elimination rule matches
		if( !subthy.find_thm(Thy::ELIM,[&]( Import const& import, Thm const& thm, ThmInfo const& info )->Opt<Thm>{
			auto elim = info.ref<Elim>();
			assert(elim);
			if( auto m = elim->matches(assm) ) {
				auto const& res = elim->instantiate(*m,assm,import);
				elim_res.emplace_back(res);
				n_elim_res++;
				return {thm};
			}
			return {};
		}) ) {
			// no elimination matches, so just declare the assumption as forced
			add_forced(subthy,assm,ctrl.force_assms);
		}
	}
	// try exact conclusions
	if( !subthy.find_thm( Thy::EXACT, [&]( Import const& import, Thm const& thm, ThmInfo const& info )->Opt<Thm>{
		auto thm2 = thm.subst(import);
		if( thm2 == goal ) {
			_thm = _thm.discharge(thm2.intro());
			return {thm2};
		}
		return {};
	} ) ) {
		fuel--;
		auto thesis = claim_exact(subthy,goal);
		auto const& subgoal_child = subthy.branch();
		auto const& sub2subsub = *subgoal_child.parent();
		auto const& g = subgoal_child.weaken(thesis._claim);
		auto intro_tester = [&]( Import const& import, Thm const& thm, ThmInfo const& info )->Opt<Thm>{
			auto const& rule = info.ref<Intro>();
			assert(rule);
			auto const& m = rule->matches(g);
			if( !m ) return {};
			thesis._apply2(*m,*rule,subgoal_child,import.compose(sub2subsub));
			return {thm};
		};
		auto weak_tester = [&]( Import const& import, Thm const& thm, ThmInfo const& info )->Opt<Thm>{
			auto const& rule = info.ref<Intro>();
			assert(rule);
			auto const& m = rule->matches(goal);
			if( m && thesis._apply_blast(*m,import,fuel,trial,*rule,ctrl) ) {
				return {thm};
			}
			return {};
		};
		if( !subthy.find_thm(Thy::CONCL,intro_tester) &&
			!subthy.find_thm(Thy::INTRO,intro_tester)
		) {
			for(;;) {
				if( elim_res_ind < elim_res.size() ) {// process elimination result
					if( thesis._apply(elim_res[elim_res_ind],g,subgoal_child) ) {
						elim_res_ind++;
						break;// move on to the new thesis
					}
					// the elimination result was not applicable, mark it as a forced rule and process more elimination results
					add_forced(subthy,subthy.weaken(elim_res[elim_res_ind].thm()),true);
					elim_res_ind++;
					continue;
				} else {// no more elimination result
					if( !(ctrl.rewrite && [&]( auto rew ){ return _thy.rewriter()->apply(rew.first,thesis,rew.second); }) &&
						!(trial > 0 && ( trial--, subthy.find_thm(Thy::WEAK,weak_tester) )
					) ) {
						if( fail ) return false;
						if( ctrl.log > 1 ) {
							cerr_proof_thms(subgoal_child);
						}
						throw BlastError("\"failed to blast\"")(g);
					}
					break;
				}
			}
		}
		// blast all new subgoals:
		while( thesis._goals > 0 ) {
			if( !thesis._blast(fuel,trial,ctrl,fail,elim_res,elim_res_ind) ) {
				return false;
			}
		}
		_thm = _thm.discharge(thesis._thm.intro());
	}
	_goals--;
	for( int i = 0; i < n_elim_res; i++ ) {// clean up elim results
		elim_res.pop_back();
	}
	return true;
}

Opt<Thm> proves( CTerm const& claim, Thy const& thy ) {
	return proves(claim,thy,Inference::DEFAULT_CTRL);
}

Thm prove( CTerm const& claim, Thy const& thy ) {
	return prove(claim,thy,Inference::DEFAULT_CTRL);
}

