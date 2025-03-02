#include "inference.hpp"
using namespace std;

string const Inference::EXACT = "#exact";
string const Inference::CONCL = "#concl";
string const Inference::INTRO = "#intro";

CTerm dummy( Ctxt const& ctxt ) {
	return ctxt.cterm(DUMMY);
}
Error const Inference::NoGoal = Error("\"no goal to apply\"");
Error const Inference::Unapplicable = Error("\"apply failed\"");

Intro Intro::imp( Thm const& thm ) {
	Ctxt ctxt = thm.ctxt().branch();
	Thm rule = strip_all(thm,ctxt);
	auto imp = rule.cbinary(IMP);
	assert(imp);
	rule = rule.discharge(ctxt.assume(imp->first));
	rule = strip_all(rule,ctxt);
	return Intro(rule);
}

Intro Intro::rule( Thm const& thm ) {
	Ctxt ctxt = thm.ctxt().branch();
	Thm rule = strip_all(thm,ctxt);
	while( auto imp = rule.cbinary(IMP) ) {
		rule = rule.discharge(ctxt.assume(imp->first));
		rule = strip_all(rule,ctxt);
	}
	return Intro(rule);
}
Elim Elim::rule( Thm const& thm ) {
	Ctxt ctxt = thm.ctxt().branch();
	Thm body = strip_all(thm,ctxt);
	auto imp = body.cbinary(IMP);
	if( !imp ) throw Error("\"malformed elimination rule\"")(thm);
	Thm premise = ctxt.assume(imp->first);
	body = body.discharge(premise);
	auto all = body.binder(ALL);
	if( !all ) throw Error("\"malformed elimination rule\"")(thm);
	return Elim(premise,body);
}

void add_forced( Locale& loc, Thm const& thm, bool allow_intro ) {
	if( auto all = thm.cbinder(ALL) ) {
		if( strip_all(all->second).binary(IMP) ) {
			loc.add_thm(Inference::INTRO,thm);
		} else {
			loc.add_thm(Inference::CONCL,thm);
		}
	} else if( thm.binary(IMP) ) {
		loc.add_thm(Inference::INTRO,thm);
	} else {
		loc.add_thm(Inference::EXACT,thm);
	}
}
void Inference::_apply( std::set<Intro> const& rules, size_t& suc, size_t min, size_t max, bool safe, bool deep ) & {
	for(;;) {
		if( _goals == 0 ) {
			if( suc < min ) throw Error("\"no more goal to apply on\"");
			return;
		}
		if( suc == max ) {
			if( !safe ) throw Error("\"apply limit exceeded\"")(to_string(max));
			return;
		}
		if( !_apply(rules,strip_all(goal())) ) {
			break;
		}
		suc++;
	}
	if( deep && push() ) {
		_apply(rules,suc,min,max,safe,deep);
		pop();
	}
	if( suc < min ) throw Error("\"apply failed\"");
}

bool Inference::_apply( Intro const& rule, CTerm const& goal ) & {
	auto const& m = rule.matches(goal);
	if( !m ) return false;
	auto ctxt = goal.ctxt();// collects new assumptions
	auto rule_intp = rule.intp(ctxt);
	while( auto const& v = rule_intp.fixing() ) {// instantiate rule variables
		if( auto const& val = m->get(*v) ) {
			rule_intp.instantiate(*val);
		} else {
			rule_intp.instantiate(dummy(ctxt));
		}
	}
	while( auto const& assm = rule_intp.assuming() ) {// make assumptions
		rule_intp.discharge(ctxt.assume(*assm));
		_goals++;
	}
	auto claim = rule.inst(rule_intp);
	_thm = _thm.weaken(ctxt).discharge(claim).intro();
	_goals--;
	return true;
}

void Inference::_blast(
	size_t& fuel,
	set<Intro> const& intros,
	set<Elim> const& elims,
	function<bool(Inference&)> extra,
	vector<Intro>& elim_res,
	size_t elim_res_ind
) & {
	if( _goals == 0 ) {// no goal to blast
		throw Error("\"no goal to blast\"");
	}
	if( fuel == 0 ) {
		throw Error("\"blast limit exceeded\"");
	}
DEB(goal());
	auto const& imp = _thm.cbinary(IMP);
	assert(imp);
	auto subloc = _loc.branch();
	auto goal = strip_all(imp->first,subloc);
	size_t n_elim_res = 0;
	while( auto imp = goal.cbinary(IMP) ) {// make assumptions
		auto assm = subloc.assume(imp->first);
		goal = imp->second;
DEB( assm << " then " << goal );
		for( auto elim : elims ) {// checks if an elimination rule matches
			if( auto o = elim.matches(assm) ) {
				// goal: φθ ⟹ χ, elim_res: ∀thesis. ψθ... ⟹ thesis
				elim_res.push_back(*o);
				n_elim_res++;
			}
		}
		// no elimination matches, so just declare the assumption as forced
		add_forced(subloc,assm);
	}
	// try exact conclusions
	if( !subloc.find_thm( EXACT, [&]( auto& thm ){
		return thm == goal ? _thm = _thm.discharge(thm.intro()), true : false;
	} ) ) {
		auto thesis = claim_exact(subloc,goal);
		auto const& g = thesis._claim.weaken(thesis._claim.ctxt().branch());
		if( !subloc.find_thm( CONCL, [&]( auto& thm ){ return thesis._apply(Intro::axiom(thm),g); } ) ) {
			fuel--;
			if( !extra(thesis) &&
				!thesis._apply(intros,g) &&
				!subloc.find_thm( INTRO, [&]( auto& thm ){ return thesis._apply(Intro::rule(thm),g); } )
			) {
				if( elim_res_ind < elim_res.size() ) {// apply elimination result
					thesis._apply(elim_res[elim_res_ind],g);
					elim_res_ind++;
				} else {
					DEB(subloc.print_thms(EXACT));
					throw Error("\"failed to blast\"")(goal);
				}
			}
			// blast all new subgoals:
			while( thesis._goals > 0 ) {
				thesis._blast(fuel,intros,elims,extra,elim_res,elim_res_ind);
			}
		}
		_thm = _thm.discharge(thesis._thm.intro());
	}
	_goals--;
	for( int i = 0; i < n_elim_res; i++ ) {// clean up elim results
		elim_res.pop_back();
	}
	return;
}