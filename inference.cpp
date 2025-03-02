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

void Inference::blast( size_t& fuel, set<Intro> const& intros, set<Elim> const& elims, function<bool(Inference&)> extra ) & {
	if( _goals == 0 ) {// no goal to blast
		throw Error("\"no goal to blast\"");
	}
	auto const& imp = _thm.cbinary(IMP);
	assert(imp);
	auto subloc = _loc.branch();
	auto goal = strip_all(imp->first,subloc);
	while( auto imp = goal.cbinary(IMP) ) {// make assumptions
		auto assm = subloc.assume(imp->first);
		goal = imp->second;
		for( auto elim : elims ) {// checks if an elimination rule matches
			if( auto o = elim.matches(assm) ) {
				// apply the rule on the remaining goal.
				auto intp = elim.intp(subloc);
				while( auto const& sym = intp.fixing() ) {
					auto const& val = o->get(*sym);
					intp.instantiate( val ? *val : goal );
				}
				auto thesis = claim_exact(subloc,goal);
				thesis.apply(Intro::rule(elim.subst(intp)));
				fuel--;
				// as this can produce new goals, blast all return the conclusion.
				thesis.blast_all(fuel,intros,elims,extra);
				_thm = _thm.discharge(thesis._thm.intro());
				_goals--;
				return;
			}
		}
		// no elimination matches, so just declare the assumption forced
		add_forced(subloc,assm);
	}
	// No elimination was applied. Try to conclude.
	auto thesis = claim_exact(subloc,goal);
	// try exact conclusions
	if( !subloc.find_thm( EXACT, [&]( auto& thm ){ return thesis._discharges(thm); } ) )
	// try extra method
	if( !extra(thesis) ) {
		auto const& g = thesis._claim.weaken(thesis._claim.ctxt().branch());
		// try explicitly given rules
		if( !thesis._apply(intros,g) )
		// try schematic conclusions
		if( !thesis._loc.find_thm( CONCL, [&]( auto& thm ){ return thesis._apply(Intro::axiom(thm),g); } ) )
		// try forced rules
		if( !thesis._loc.find_thm( INTRO, [&]( auto& thm ){ return thesis._apply(Intro::rule(thm),g); } ) )
			throw Error("\"failed to blast\"")(goal);
	}
	// blast all new subgoals:
	fuel--;
	thesis.blast_all(fuel,intros,elims,extra);
	_thm = _thm.discharge(thesis._thm.intro());
	_goals--;
	return;
}