#include "concluder.hpp"

using namespace std;

Thm Concluder::conclude(Thm const& thesis) {
	if( auto const& imp = thesis.cbinary(IMP) ) {
		auto const& goal = imp->first;
		for( auto const& rule : _rules ) {
			if( auto const& m = match(rule.pat.ctxt().fvars(),rule.pat,goal) ) {
				auto const& thesis_ctxt = thesis.ctxt();
				Thm thm = rule.thm.weaken(thesis_ctxt);
				auto thm_ctxt = thm.ctxt().branch();
				thm = strip_all(thm,thm_ctxt);
				auto intp = Intp::make(thm_ctxt,thesis_ctxt);
				while( auto const& sym = intp.fixing() ) {
					intp.instantiate(*m->get(*sym));
				}
				return thesis.impE(intp.subst(thm));
			}
		}
		throw Error("\"nontrivial conclusion\"")(thesis);
	}
	throw Error("\"no goal to conclude\"");
}

