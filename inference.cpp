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
void Inference::apply( std::set<Rule> const& rules, size_t min, size_t max, bool safe ) & {
	for( int i = 0;; i++ ) {
		if( i == max ) {
			if( safe ) return;
			throw Error("\"apply limit exceeded\"")(to_string(max));
		}
		if( _goals == 0 ||
			!_apply(rules,goal().weaken(_thm.ctxt().branch())) ) {
			if( i < min ) throw Error("\"apply failed\"");
			return;
		}
	}
}
bool Inference::_apply( Rule const& rule, CTerm const& goal ) & {
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
		subloc.add_thm(CONCL,subloc.assume(imp2->first));
		subgoal = imp2->second;
	}
	auto subthesis = Inference(subloc,subgoal);
	auto g = subgoal.weaken(subgoal.ctxt().branch());
	if( // try explicitly given rules
		!subthesis._apply(rules,g) &&
		// try assumptions as conclusion. Not as rules, as it can be a wrong choice
		!subloc.find_thm( CONCL, [&](auto& thm){ return subthesis._apply(axiom(thm),g); } ) &&
		// try environmental rules
		!subloc.find_thm( INTRO, [&](auto& thm){ return subthesis._apply(rule(thm),g); } )
	) {
		throw Error("\"failed blast\"")(subgoal);
	}
	// blast all sub-sub-goals:
	fuel--;
	while( subthesis._goals > 0 ) {
		if( fuel == 0 ) throw Error("\"blast exceeded\"")(*subthesis.has_goal());
		subthesis.blast(rules,fuel);
	}
	_thm = _thm.impE(subthesis._thm.intro());
	_goals--;
	return;
}