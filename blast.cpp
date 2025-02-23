#include "locale.hpp"
using namespace std;

CTerm dummy( Ctxt const& ctxt ) {
	return ctxt.cterm(DUMMY);
}

Rule Rule::make( Thm const& thm ) {
	Ctxt ctxt = thm.ctxt().branch();
	Thm rule = strip_all(thm,ctxt);
	while( auto imp = rule.cbinary(IMP) ) {
		rule = rule.impE(ctxt.assume(imp->first));
		rule = strip_all(rule,ctxt);
	}
	return rule;
}
void Thesis::discharge( Thm const& thm ) {
	if( _goals == 0 ) throw Error("\"no goal to discharge\"");
	_thm = _thm.impE(thm);
	_goals--;
}
bool Thesis::apply( Rule const& rule ) & {
	if( _goals == 0 ) throw Error("\"no goal to apply\"");
	auto const& imp = _thm.cbinary(IMP);
	assert(imp);
	auto const& m = rule.matches(imp->first);
	if( !m ) return false;
	auto& ctxt = _thm.ctxt().branch();// collects requirements for the rule
	auto& intp = rule.intp(ctxt);
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

bool Thesis::apply( set<Rule> const& rules ) & {
	for( auto const& rule : rules ) {
		if( apply(rule) ) return true;
	}
	return false;
}
void Thesis::apply( std::set<Rule> const& rules, size_t min, size_t max, bool safe ) & {
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
bool Thesis::blast( set<Rule> const& rules, size_t& fuel ) & {
	if( _goals == 0 ) {// no goal to blast
		return {};
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
	auto& subthesis = Thesis(subloc,subgoal);
	if( // try explicitly given rules
		!subthesis.apply(rules) ||
		// try assumptions as axioms. Not as rules, as it can be a wrong choice
		!_loc.find_thm( ASSM, [&](auto& thm){ return subthesis.apply(Rule::axiom(thm)); } ) ||
		// try environmental rules
		!_loc.find_thm( INTRO, [&](auto& thm){ return subthesis.apply(Rule::make(thm)); } )
	) {
		throw Error("\"failed blast\"")(subgoal);
	}
	// blast all sub-sub-goals:
	fuel--;
	for(;;) {
		if( fuel > 0 )
		if( subthesis.blast(rules,fuel) ) {
			continue;
		}
		break;
	}
	if( subthesis._goals > 0 ) {
		auto const& imp = subthesis._thm.cbinary(IMP);
		assert(imp);
		throw Error("\"failed to blast\"")(imp->first);
	}
	_thm = _thm.impE(subthesis._thm);
}