#include "concluder.hpp"

using namespace std;

Thm conclude( CSubst const& matcher, Thm const& thesis, Thm const& thm_strip ) {
	auto const& thm_vars = thm_strip.ctxt();
	auto intp = Intp(thm_vars,thesis.ctxt());
	while( auto const& sym = intp.fixing() ) {
		auto const& val = matcher.get(*sym);
		intp.instantiate( val ? *val : thesis.ctxt().cterm(DUMMY));
	}
	return thesis.discharge(intp.subst(thm_strip));
}
Opt<Thm> concludes( CTerm const& goal, Thm const& thesis, CTerm const& pat, Thm const& thm ) {
	if( auto const& m = match(pat,goal,[&](auto v){ return pat.ctxt().fixes(v); }) ) {
		auto const& thesis_ctxt = thesis.ctxt();
		auto thm_vars = thesis_ctxt.branch();
		Thm thm_strip = strip_all(thm,thm_vars);
		return conclude(*m,thesis,thm_strip);
	}
	return {};
}
Thm Concluder::conclude(Thm const& thesis) {
	if( auto const& imp = thesis.cbinary(IMP) ) {
		auto const& goal = imp->first;
		for( auto const& [pat,thm] : _rules ) {
			if( auto const& ret = concludes(goal,thesis,pat,thm) ) {
				return *ret;
			}
		}
		throw Error("\"nontrivial conclusion\"")(thesis);
	}
	throw Error("\"no goal to conclude\"");
}

