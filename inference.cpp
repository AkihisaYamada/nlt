#include "inference.hpp"
using namespace std;

string const Inference::EXACT = "#exact";
string const Inference::CONCL = "#concl";
string const Inference::INTRO = "#intro";
string const Inference::WEAK = "#weak";

CTerm dummy( Ctxt const& ctxt ) {
	return ctxt.cterm(DUMMY);
}
Error const Inference::NoGoal = Error("\"no goal to apply\"");
Error const Inference::Unapplicable = Error("\"apply failed\"");

Intro Intro::imp( Thm const& thm, size_t n ) {
	auto child = thm.ctxt().branch();
	Thm rule = thm.subst(child);
	size_t vars = 0;
	for( size_t i = 0;; i++ ) {
		if( i == n ) return Intro(thm,rule,vars,i);
		auto const& [rule2,vars2] = strip_all(rule,child);
		vars += vars2;
		auto imp = rule2.cbinary(IMP);
		assert(imp);
		rule = rule2.discharge(child.ctxt().assume(imp->first));
	}
}

Intro Intro::rule( Thm const& thm ) {
	auto [rule,child,vars] = strip_all(thm);
	auto ctxt = child.ctxt();
	size_t conds = 0;
	while( auto imp = rule.cbinary(IMP) ) {
		rule = rule.discharge(ctxt.assume(imp->first));
		conds++;
		rule = strip_all(rule,ctxt.self()).first;
	}
	return Intro(thm,rule,vars,conds);
}
Elim Elim::rule( Thm const& thm ) {
	auto child = thm.ctxt().branch();
	Thm body = strip_all(thm,child).first;
	auto imp = body.cbinary(IMP);
	if( !imp ) throw Error("\"malformed elimination rule\"")(thm);
	Thm premise = child.ctxt().assume(imp->first);
	body = body.discharge(premise);
	return Elim(premise,body);
}

void add_forced( Thy& thy, Thm const& thm, bool allow_intro ) {
	auto intro = Intro::rule(thm);
	if( intro.conds() > 0 ) {
		thy.add_thm( allow_intro ? Inference::INTRO : Inference::WEAK, thm, {intro} );
	} else if( intro.vars() > 0 ) {
		thy.add_thm(Inference::CONCL,thm,{intro});
	} else {
		thy.add_thm(Inference::EXACT,thm);
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
		if( !_apply(rules,goal().subst(child),child) ) {
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
	size_t& fuel,
	size_t trial,
	CTerm const& goal,// belong to _thy
	Intro const& rule,
	Ctrl const& ctrl
) & {
	auto const& m = rule.matches(goal);
	if( !m ) return false;
	// interpret the context where the theorem to apply is proved.
	auto rule_intp = _thy.interpret_ancestor(rule.thm().ctxt());
	// then interpret the context holding the pattern variables and premises.
	auto pat_intp = rule_intp.interpret(rule.conclusion().ctxt());
	while( auto const& v = pat_intp.fixing() ) {// instantiate pattern variables
		if( auto const& val = m->get(*v) ) {
			pat_intp.instantiate(*val);
		} else {
			pat_intp.instantiate(dummy(_thy));
		}
	}
	while( auto const& assm = pat_intp.assuming() ) {// discharge assumptions
		Inference thesis = claim_exact(_thy,*assm);
		vector<Intro> elim_res;
		if( !thesis._blast(fuel,trial,ctrl,true,elim_res,0) ) return false;
		pat_intp.discharge(thesis._thm);
	}
	auto claim = rule.subst(pat_intp);
	_thm = _thm.discharge(claim);
	_goals--;
	return true;
}

bool Inference::_apply( Intro const& rule, CTerm const& goal, Import const& child ) & {
	auto const& m = rule.matches(goal);
	if( !m ) return false;
	// interpret the context where the theorem to apply is proved.
	auto rule2child = child.thy().interpret_ancestor(rule.thm().ctxt());
	// then interpret the context holding the pattern variables and premises.
	auto pat2child = rule2child.interpret(rule.conclusion().ctxt());
	auto ctxt = goal.ctxt();// collects new assumptions
	for(;;) {
		if( auto const& v = pat2child.fixing() ) {// instantiate pattern variables
			if( auto const& val = m->get(*v) ) {
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
	_thm = _thm.subst(child).discharge(rule.subst(pat2child)).intro();
	_goals--;
	return true;
}

bool Inference::_blast(
	size_t& fuel,
	size_t trial,
	Ctrl const& ctrl,
	bool fail,
	vector<Intro>& elim_res,
	size_t elim_res_ind
) & {
	if( _goals == 0 ) {// no goal to blast
		throw Error("\"no goal to blast\"");
	}
	if( fuel == 0 ) {
		if( fail ) return false;
		throw Error("\"blast limit exceeded\"");
	}
	auto const& imp = _thm.cbinary(IMP);
	assert(imp);
	auto const& child = _thy.branch();
	auto subthy = child.thy();
	auto goal = imp->first.subst(child);
	size_t n_elim_res = 0;
	for(;;) {
		goal = strip_all(goal,subthy.self());
		if( auto imp = goal.cbinary(IMP) ) {// make assumptions
			auto assm = subthy.assume(imp->first);
			goal = imp->second;
			if( auto rew = ctrl.rewrite ) {// rewrite the assumption
				assm = subthy.rewriter().rewrite(rew->first,subthy,assm,rew->second);
			}
			for( auto elim = ctrl.elims.begin();; elim++ ) {// checks if an elimination rule matches
				if( elim == ctrl.elims.end() ) {
					// no elimination matches, so just declare the assumption as forced
					add_forced(subthy,assm,ctrl.force_assms);
					break;
				}
				if( auto o = elim->matches(assm,child/*FIX!*/) ) {
					// goal: φθ ⟹ χ, elim_res: ∀thesis. ψθ... ⟹ thesis
					elim_res.push_back(*o);
					n_elim_res++;
					break;
				}
			}
			continue;
		}
		break;
	}
	// try exact conclusions
	if( !subthy.find_thm( EXACT, [&]( auto& thm ){
		return thm == goal ? _thm = _thm.discharge(thm.intro()), true : false;
	} ) ) {
		fuel--;
		auto thesis = claim_exact(subthy,goal);
		auto subgoal_child = subthy.branch();
		auto const& g = thesis._claim.subst(subgoal_child);
		if( !subthy.find_thm( CONCL, [&]( auto& thm ){ return thesis._apply(Intro::axiom(thm),g,subgoal_child); } ) ) {
			if( !(ctrl.rewrite && [&]( auto rew ){ return _thy.rewriter().apply(rew.first,thesis,rew.second); }) &&
				!thesis._apply(ctrl.intros,g,subgoal_child) &&
				!subthy.find_thm( INTRO, [&]( auto& thm ){ return thesis._apply(Intro::rule(thm),g,subgoal_child); } )
			) {
				for(;;) {
					if( elim_res_ind == elim_res.size() ) {
						if( trial == 0 ||
							( trial--,
							 !subthy.find_thm( WEAK, [&]( auto& thm ){
								return thesis._apply_blast(fuel,trial,goal,Intro::rule(thm),ctrl);
							} ) )
						) {
							if( fail ) return false;
							throw Error("\"failed to blast\"")(goal);
						}
						break;
					}
// apply elimination result
					if( !thesis._apply(elim_res[elim_res_ind],g,subgoal_child) ) {
						add_forced(subthy,elim_res[elim_res_ind].thm(),true);
					}
					elim_res_ind++;
					break;
				}
			}
			// blast all new subgoals:
			while( thesis._goals > 0 ) {
				if( !thesis._blast(fuel,trial,ctrl,fail,elim_res,elim_res_ind) ) {
					return false;
				}
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
