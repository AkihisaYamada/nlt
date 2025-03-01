#include "inference.hpp"
using namespace std;

string const Inference::INTRO = "#intro";
string const Inference::CONCL = "#concl";
string const Inference::EXACT = "#exact";

CTerm dummy( Ctxt const& ctxt ) {
	return ctxt.cterm(DUMMY);
}
Error const Inference::NoGoal = Error("\"no goal to apply\"");
Error const Inference::Unapplicable = Error("\"apply failed\"");

Inference::Rule Inference::imp( Thm const& thm ) {
	Ctxt ctxt = thm.ctxt().branch();
	Thm rule = strip_all(thm,ctxt);
	auto imp = rule.cbinary(IMP);
	assert(imp);
	rule = rule.impE(ctxt.assume(imp->first));
	rule = strip_all(rule,ctxt);
	return Rule(rule);
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
void add_forced( Locale& loc, Thm const& thm ) {
	if( auto all = thm.binder(ALL) ) {
		if( all->second.binary(IMP) ) {
			loc.add_thm(Inference::INTRO,thm);
		} else {
			loc.add_thm(Inference::CONCL,thm);
		}
	} else {
		loc.add_thm(Inference::EXACT,thm);
	}
}

void Inference::_apply( std::set<Rule> const& rules, size_t& suc, size_t min, size_t max, bool safe, bool deep ) & {
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

Opt<Thm> blasts( Thm const& thesis, Locale const& loc, std::set<Inference::Rule> const& rules ) {
	if( auto imp = thesis.cbinary(IMP) ) {
		return thesis.impE(prove(imp->first,loc,rules));
	}
	return {};
}

Thm prove( CTerm const& claim, Locale const& loc, std::set<Inference::Rule> const& rules ) {
	auto x = Inference::claim_strip(loc,claim);
	size_t fuel = 255;
	x.blast(rules,fuel);
	return x.concluding()->intro();
}

void Inference::blast( set<Rule> const& rules, size_t& fuel, std::function<bool(Inference&)> extra ) & {
	if( _goals == 0 ) {// no goal to blast
		throw Error("\"no goal to blast\"");
	}
	auto const& imp = _thm.cbinary(IMP);
	assert(imp);
	auto const& goal = imp->first;
	auto thesis = claim_strip(_loc,goal);
	// try exact conclusions
	if( !thesis._loc.find_thm( EXACT, [&]( auto& thm ){ return thesis._discharges(thm); } ) )
	// try extra method
	if( !extra(thesis) ) {
		auto const& g = thesis._claim.weaken(thesis._claim.ctxt().branch());
		// try explicitly given rules
		if( !thesis._apply(rules,g) )
		// try schematic conclusions
		if( !thesis._loc.find_thm( CONCL, [&]( auto& thm ){ return thesis._apply(axiom(thm),g); } ) )
		// try forced rules
		if( !thesis._loc.find_thm( INTRO, [&]( auto& thm ){ return thesis._apply(rule(thm),g); } ) )
			throw Error("\"failed to blast\"")(goal);
	}
	// blast all new subgoals:
	fuel--;
	while( thesis._goals > 0 ) {
		if( fuel == 0 ) throw Error("\"blast exceeded\"")(*thesis.has_goal());
		thesis.blast(rules,fuel,extra);
	}
	_thm = _thm.impE(thesis._thm.intro());
	_goals--;
	return;
}