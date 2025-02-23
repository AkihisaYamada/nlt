#include "inference.hpp"
using namespace std;

CTerm dummy( Ctxt const& ctxt ) {
	return ctxt.cterm(DUMMY);
}

Inference::Rule Inference::rule( Thm const& thm ) {
	Ctxt ctxt = thm.ctxt().branch();
	Thm rule = strip_all(thm,ctxt);
	while( auto imp = rule.cbinary(IMP) ) {
		rule = rule.impE(ctxt.assume(imp->first));
		rule = strip_all(rule,ctxt);
	}
	return Rule(rule);
}
void Inference::discharge( Thm const& thm ) {
	if( _goals == 0 ) throw Error("\"no goal to discharge\"");
	_thm = _thm.impE(thm);
	_goals--;
}
bool Inference::apply( Rule const& rule ) & {
	if( _goals == 0 ) throw Error("\"no goal to apply\"");
	auto const& imp = _thm.cbinary(IMP);
	assert(imp);
	auto const& m = rule.matches(imp->first);
	if( !m ) return false;
	auto ctxt = _thm.ctxt().branch();// collects requirements for the rule
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
	_thm = _thm.weaken(ctxt).impE(rule.inst(intp)).intro();
	return true;
}

bool Inference::apply( set<Rule> const& rules ) & {
	for( auto const& rule : rules ) {
		if( apply(rule) ) return true;
	}
	return false;
}
void Inference::apply( std::set<Rule> const& rules, size_t min, size_t max, bool safe ) & {
	for( int i = 0;; i++ ) {
		if( i == max ) {
			if( safe ) break;
			throw Error("\"apply limit exceeded\"")(to_string(max));
		}
		if( apply(rules) ) {
			continue;
		}
		if( i < min ) {
			throw Error("\"Rule not applicable\"");
		}
		return;
	}
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
		!subthesis.apply(rules) ||
		// try assumptions as axioms. Not as rules, as it can be a wrong choice
		!_loc.find_thm( ASSM, [&](auto& thm){ return subthesis.apply(axiom(thm)); } ) ||
		// try environmental rules
		!_loc.find_thm( INTRO, [&](auto& thm){ return subthesis.apply(rule(thm)); } )
	) {
		throw Error("\"failed blast\"")(subgoal);
	}
	// blast all sub-sub-goals:
	fuel--;
	while( subthesis._goals > 0 ) {
		if( fuel == 0 ) throw Error("\"blast exceeded\"")(*subthesis.goal());
		subthesis.blast(rules,fuel);
	}
	_thm = _thm.impE(subthesis._thm);
	return;
}