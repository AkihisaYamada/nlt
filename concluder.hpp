#ifndef _CONCLUDER_HPP_
#define _CONCLUDER_HPP_

#include"util.hpp"

Thm conclude( Subst const& matcher, Thm const& thesis, Thm const& thm );
Opt<Thm> concludes( CTerm const& goal, Thm const& thesis, CTerm const& pat, Thm const& thm );
Opt<Thm> concludes( Thm const& thesis, Thm const& thm );

/** @brief Discharges assumption that match one of the rules. */
class Concluder {
	struct _Rule {
		CTerm pat;
		Thm thm;
	};
	std::vector<_Rule> _rules;
public:
	void insert(Thm const& thm) {
		auto pat_ctxt = thm.ctxt().fork();
		auto const& pat = strip_all(thm,pat_ctxt,fresh_maker());
		_rules.emplace_back(pat,pat.intro());
	}
	/** Discharge assumption that matches one of the rules. */
	Thm conclude(Thm const& target);
};

#endif
