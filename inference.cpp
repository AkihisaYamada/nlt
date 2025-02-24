#include "inference.hpp"
using namespace std;

CTerm dummy( Ctxt const& ctxt ) {
	return ctxt.cterm(DUMMY);
}
Error const Inference::NoGoal = Error("\"no goal to apply\"");
Error const Inference::Unapplicable = Error("\"apply failed\"");

Inference::Rule Inference::rule( Thm const& thm ) {
	Ctxt ctxt = thm.ctxt().branch();
	Thm rule = strip_all(thm,ctxt);
	while( auto imp = rule.cbinary(IMP) ) {
		rule = rule.impE(ctxt.assume(imp->first));
		rule = strip_all(rule,ctxt);
	}
	return Rule(rule);
}
pair<Ctxt,CTerm> Inference::_init_thesis() const {
	if( _goals == 0 ) throw NoGoal;
	auto ctxt = _thm.ctxt().branch();// fixes variables and collects requirements for the rule
	auto imp = strip_all(_thm,ctxt);
	auto const& p = imp.cbinary(IMP);
	assert(p);
	return {ctxt,p->first};
}
void Inference::apply( std::set<Rule> const& rules, size_t min, size_t max, bool safe ) & {
	auto [ctxt,goal] = _init_thesis();
	for( int i = 0;; i++ ) {
		if( i == max ) {
			if( safe ) break;
			throw Error("\"apply limit exceeded\"")(to_string(max));
		}
		if( _apply(rules,ctxt,goal) ) {
			continue;
		}
		if( i < min ) {
			throw Error("\"Rules not applicable\"");
		}
		return;
	}
}
bool Inference::_apply( Rule const& rule, Ctxt& ctxt, CTerm const& goal ) & {
	auto const& m = rule.matches(goal);
	if( !m ) return false;
	auto intp = rule.intp(ctxt);
	while( auto const& v = intp.fixing() ) {// instantiate rule variables
		if( auto const& val = m->get(*v) ) {
			intp.instantiate(*val);
		} else {
			intp.instantiate(dummy(ctxt));
		}
	}
	while( auto const& assm = intp.assuming() ) {// make assumptions
		intp.discharge(ctxt.assume(*assm));
		_goals++;
	}
	auto claim = rule.inst(intp);
	_thm = _thm.weaken(ctxt).impE(claim).intro();
	_goals--;
	return true;
}

void Inference::blast( set<Rule> const& rules, size_t& fuel ) & {
	if( _goals == 0 ) {// no goal to blast
		throw Error("\"no goal to blast\"");
	}
	auto const& imp = _thm.cbinary(IMP);
	assert(imp);
	auto const& goal = imp->first;
	Locale subloc = _loc.branch();
	CTerm subgoal = strip_all(goal,subloc);
	while( auto const& imp2 = subgoal.cbinary(IMP) ) {// make assumptions for the subgoal
		subloc.assume(ASSM,imp2->first);
		subgoal = imp2->second;
	}
	auto subthesis = Inference(subloc,subgoal);
	if( // try explicitly given rules
		!subthesis._apply(rules,subloc,subgoal) &&
		// try assumptions as axioms. Not as rules, as it can be a wrong choice
		!_loc.find_thm( ASSM, [&](auto& thm){ return subthesis._apply(axiom(thm),subloc,subgoal); } ) &&
		// try environmental rules
		!_loc.find_thm( INTRO, [&](auto& thm){ return subthesis._apply(rule(thm),subloc,subgoal); } )
	) {
		throw Error("\"failed blast\"")(subgoal);
	}
	// blast all sub-sub-goals:
	fuel--;
	while( subthesis._goals > 0 ) {
		if( fuel == 0 ) throw Error("\"blast exceeded\"")(*subthesis.goal());
		subthesis.blast(rules,fuel);
	}
	_thm = _thm.impE(subthesis._thm.intro());
	_goals--;
	return;
}