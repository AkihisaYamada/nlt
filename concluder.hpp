#ifndef _CONCLUDER_HPP_
#define _CONCLUDER_HPP_

#include"util.hpp"

/** @brief Discharges assumption that match one of the rules. */
class Concluder {
	struct _Rule {
		CTerm pat;
		Thm thm;
	};
	std::vector<_Rule> _rules;
public:
	void insert(Thm const& thm) {
		auto pat_ctxt = thm.ctxt().branch();
		auto const& pat = strip_all(thm,pat_ctxt);
		_rules.emplace_back(pat,thm);
	}
	/** Discharge assumption that matches one of the rules. */
	Thm conclude(Thm const& target);
};

#endif
