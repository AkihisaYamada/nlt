#include "inference.hpp"
using namespace std;

string const EXACT = "#exact";
string const CONCL = "#concl";
string const INTRO = "#intro";
string const WEAK = "#weak";
string const ELIM = "#elim";
string const INF = "#inf";

string const SIMP = "#simp";
string const CONG = "#cong";
string const DUAL = "#dual";

void cerr_proof_thms( Thy const& thy ) {
	for( auto const& name : { EXACT, CONCL, INTRO, WEAK, ELIM, INF } ) {
		cerr << name << ":" << thy.print_thms(name);
	}
}

CTerm dummy( Ctxt const& ctxt ) {
	return ctxt.cterm(DUMMY);
}

Intro Intro::imp( Thm const& thm, size_t n, bool all ) {
	auto child = thm.ctxt().fork();
	auto self = child.ctxt().self();
	auto f = patvar_maker();
	Thm rule = thm.subst(child);
	size_t vars = 0;
	size_t i = 0;
	for( ;; i++ ) {
		if( i == n && !all ) break;
		auto const& [rule2,vars2] = strip_all(rule,self,f);
		rule = rule2;
		vars += vars2;
		if( i == n ) break;
		auto imp = rule.cbinary(IMP);
		if( !imp ) {
			if( n != 255 ) throw Error("\"making intro rule failed\"")(thm);
			break;
		}
		rule = rule.impE(child.ctxt().assume(imp->first));
	}
	return Intro(thm,rule,vars,i);
}

Intro Intro::rule( Thm const& thm ) {
	return imp(thm,255,true);
}
Elim Elim::rule( Thm const& thm, short after, char mode ) {
	auto child = thm.ctxt().fork();
	Thm body = strip_all(thm,child,patvar_maker()).first;
	auto imp = body.cbinary(IMP);
	if( !imp ) throw Error("\"malformed elimination rule\"")(thm);
	Thm premise = child.ctxt().assume(imp->first);
	body = body.impE(premise);
	return Elim(thm,premise,body,after,mode);
}
std::pair<std::string,AThm> Elim::instantiate( Subst& m, Thm const& arg, Intp const& intp, Thy const& thy ) const {
	auto pat_ctxt = _premise.ctxt();
	auto thm_ctxt = _thm.ctxt();
	auto pat2loc = Intp::make(pat_ctxt,thm_ctxt).compose(intp);
	subst_intp(pat2loc,m);
	pat2loc.discharge(arg);
	auto thm = _rule.subst(pat2loc);// ∀thesis. ψθ... ⟹ thesis
	if( _after == 0 ) {
		if( _mode == '=' ) {
			auto [ind,rel,rule] = thy.rewriter(SIMP).make_rule(thm,false);
			return {SIMP+rel,{thm,rule}};
		} else if( _mode == '?' ) {
			return {WEAK,{thm,Intro::rule(thm)}};
		} else {
			return {INTRO,{thm,Intro::rule(thm)}};
		}
	}
	return {INF,{thm,Elim::rule(thm,_after-1,_mode)}};
}

void add_intro( Thy& thy, Thm const& thm, Intro const& intro, bool allow_intro ) {
	if( intro.conds() > 0 ) {
		thy.add_thm( allow_intro ? INTRO : WEAK, thm, {intro} );
	} else if( intro.vars() > 0 ) {
		thy.add_thm(CONCL,thm,{intro});
	} else {
		thy.add_thm(EXACT,thm);
	}
}
void Thesis::_apply( std::set<Intro> const& rules, size_t& suc, size_t min, size_t max, bool normalize, bool wide ) & {
	for(;;) {
		if( _goals == 0 ) {
			if( suc < min ) throw Error("\"no more goal to apply on\"");
			return;
		}
		if( suc == max ) {
			if( normalize ) {
				throw Error("\"apply limit exceeded\"")(to_string(max));
			}
			return;
		}
		auto child = _thy.branch();
		if( !_apply(rules,child.weaken(goal()),child) ) {
			break;
		}
		suc++;
	}
	if( wide && push() ) {
		_apply(rules,suc,min,max,normalize,wide);
		pop();
	}
	if( suc < min ) throw Error("\"apply failed\"");
}

bool Thesis::_apply( Intro const& rule, CTerm const& goal, Thy const& child ) & {
	auto const& m = rule.matches(goal);
	if( !m ) return false;
	// interpret the context where the theorem to apply is proved.
	auto rule2child = child.interpret_ancestor(rule.thm().ctxt());
	_apply2(*m,rule,child,rule2child);
	return true;
}

void Thesis::_apply2( Subst const& matcher, Intro const& intro, Thy const& child, Intp const& rule2child ) & {
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
	_thm = child.weaken(_thm).impE(intro.conclusion().subst(pat2child)).intro();
	_goals--;
}
bool Resolver::_apply_and_discharge(
	Thesis& thesis,
	Subst const& matcher,
	Intp const& rule2child,
	size_t trial,
	Intro const& rule
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
				pat_intp.instantiate(dummy(thesis.thy()));
			}
		} else if( auto const& assm = pat_intp.assuming() ) {// discharge assumptions
			auto condthesis = Thesis::claim_exact(thesis.thy(),*assm);
			if( !_discharge(condthesis,trial,true,{SIMP},elim_res.size()) ) return false;
			pat_intp.discharge(condthesis._thm);
		} else {
			break;
		}
	}
	auto claim = rule.subst(pat_intp);
	thesis.discharge(claim);
	return true;
}

void Resolver::inflate( Thy& thy, Thm const& assm ) & {
	// one cannot update the list while reading the list.
	auto infs = vector<pair<string,AThm>>();
	thy.find_thm( INF, [&]( Import const& import, Thm const& thm, ThmInfo const& info )->Opt<Thm>{// add inferred rules
		auto elim = info.ref<Elim>();
		assert(elim);
		if( auto m = elim->matches(assm,{import}) ) {
			infs.push_back(elim->instantiate(*m,assm,import,thy));
		}
		return {};
	} );
	for( auto const& [lbl,athm] : infs ) {
		if( log > 3 ) _log() << "- inferring " << lbl << ": " << thy.pretty(athm) << "  from  " << thy.pretty(assm) << endl;
		thy.add_thm(lbl,athm,athm.info);
	}
}
bool Resolver::_discharge(
	Thesis& thesis,
	size_t trial,
	bool fail,
	Opt<std::string const&> simp,
	size_t elim_res_ind
) & {
	if( fuel == 0 ) {
		if( fail ) return false;
		if( log > 6 ) cerr_proof_thms(thesis.thy());
		throw Error("\"resolve limit exceeded\"")(thesis.goal());
	}
	auto subthy = thesis.thy().branch();
	auto goal = subthy.weaken(thesis.goal());
	if( log > 4 ) _log() << "{ resolving: " << subthy.pretty(goal) << endl;
	indent++;
	size_t n_elim_res = 0;
	for(;;) {// strip all assumptions
		goal = strip_all(goal,subthy.self());
		auto imp = goal.cbinary(IMP);
		if( !imp ) break;// no more assumption
		auto assm = subthy.assume(imp->first);// make the assumption
		goal = imp->second;
		if( simp && rew ) {// rewrite the assumption
			assm = rewrites(subthy,assm,simp,0,255,true,{});
		}
		// checks if an elimination rule matches
		if( subthy.find_thm( ELIM, [&]( Import const& import, Thm const& thm, ThmInfo const& info )->Opt<Thm>{
			auto elim = info.ref<Elim>();
			assert(elim);
			if( auto m = elim->matches(assm,{import}) ) {
				if( log > 3 ) _log() << "- eliminating: " << subthy.pretty(assm) << endl;
				elim_res.emplace_back(elim->instantiate(*m,assm,import,subthy));
				n_elim_res++;
				return {thm};
			}
			return {};
		} ) ) continue;
		// no elimination matches, declare what can be inferred from the assumption
		inflate(subthy,assm);
		add_intro(subthy,assm);
		if( log > 3 ) _log() << "- declared assumption: " << subthy.pretty(assm) << endl;
	}
	// try exact conclusions
	if( log > 5 ) _log() << "- trying to conclude: " << subthy.pretty(goal) << endl;
	if( !subthy.find_thm( EXACT, [&]( Import const& import, Thm const& thm, ThmInfo const& info )->Opt<Thm>{
		auto thm2 = thm.subst(import);
		if( thm2 == goal ) {
			thesis.discharge(thm2.intro());
			return {thm2};
		}
		return {};
	} ) ) {
		fuel--;
		auto subthesis = Thesis::claim_exact(subthy,goal);
		auto const& subgoal_child = subthy.branch();
		auto const& sub2subsub = *subgoal_child.parent();
		auto const& g = subgoal_child.weaken(subthesis._claim);
		auto intro_tester = [&]( Import const& import, Thm const& thm, ThmInfo const& info )->Opt<Thm>{
			auto const& rule = info.ref<Intro>();
			assert(rule);
			auto const& m = rule->matches(g,{import});
			if( !m ) {
				if( log > 5 ) _log() << "! intro didn't match: " << subthy.pretty(thm) << endl;
				return {};
			}
			subthesis._apply2(*m,*rule,subgoal_child,import.compose(sub2subsub));
			if( log > 3 ) _log() << "- applied: " << subthy.pretty(thm) << endl;
			return {thm};
		};
		auto weak_tester = [&]( Import const& import, Thm const& thm, ThmInfo const& info )->Opt<Thm>{
			auto const& rule = info.ref<Intro>();
			assert(rule);
			auto const& m = rule->matches(goal,{import});
			if( !m ) return {};
			if( log > 4 ) _log() << "{ trying: " << subthy.pretty(thm) << endl;
			indent++;
			if( _apply_and_discharge(subthesis,*m,import,trial,*rule) ) {
				indent--;
				return {thm};
			}
			indent--;
			return {};
		};
		if( !subthy.find_thm(CONCL,intro_tester) )
		if( !subthy.find_thm(INTRO,intro_tester) )
		for(;;) {
			if( elim_res_ind < elim_res.size() ) {// process elimination result
				auto const& [label,athm] = elim_res[elim_res_ind];
				auto const& intro = *athm.info.ref<Intro>();
				if( subthesis._apply(intro,g,subgoal_child) ) {
					if( log > 3 ) _log() << "- applied elimination result: " << subthy.pretty(athm) << endl;
				} else {
					if( log > 5 ) _log() << "- using elimination result: " << subthy.pretty(athm) << endl;
					inflate(subthy,athm);
				}
				elim_res_ind++;
				break;// move on to the new thesis
			}// no elimination result matched
			if( simp && rewrites(subthesis,simp,0,255,true,{},{}) ) {// try rewriting
				if( log > 3 ) _log() << "} rewritten: " << subthy.pretty(subthesis.goal()) << endl;
				break;
			}
			if( trial > 0 ) {
				trial--;
				if( subthy.find_thm(WEAK,weak_tester) ) break;
			}// nothing could be applied
			indent--;
			if( log > 0 ) _log() << "}! failed to resolve: " << subthy.pretty(goal) << endl;
			if( fail ) return false;
			if( log > 5 ) cerr_proof_thms(subgoal_child);
			throw Error("\"failed to resolve\"")(goal);
		}
		// prove all new subgoals:
		while( subthesis._goals > 0 ) {
			if( !_discharge(subthesis,trial,fail,simp,elim_res_ind) ) {
				indent--;
				if( log > 0 ) _log() << "}! failed to resolve: " << subthy.pretty(subthesis.goal()) << endl;
				return false;
			}
		}
		thesis.discharge(subthesis._thm.intro());
	}
	for( int i = 0; i < n_elim_res; i++ ) {// clean up elim results
		elim_res.pop_back();
	}
	indent--;
	if( log > 1 ) _log() << "} resolved: " << thesis.thy().pretty(goal) << endl;
	return true;
}

