#ifndef _INFERENCE_HPP
#define _INFERENCE_HPP

#include "locale.hpp"

/** Class for inference */
class Inference {
	Locale _loc;
	Thm _thm;
	size_t _goals;
	static Thm _make_claim( CTerm const& claim ) {
		Ctxt ctxt = claim.ctxt().branch();
		return ctxt.assume(claim.weaken(ctxt)).intro();// claim ⟹ claim
	}
public:
	/** Inference rule */
	class Rule {
		friend Inference;
		Thm _conclusion;
	public:
		explicit Rule( Thm const& conc ) : _conclusion(conc) {}
		std::function<bool(std::string_view const& v)> const fvars = [&](auto v){ return ctxt().fixes(v); };
		Thm const& conclusion() const& {
			return _conclusion;
		}
		Thm thm() const& {
			return _conclusion.intro();
		}
		Opt<CSubst> matches( CTerm const& goal ) const {
			return match( _conclusion, goal, fvars );
		}
		Ctxt ctxt() && = delete;
		Ctxt const& ctxt() const& {
			return _conclusion.ctxt();
		}
		/** @brief interpretation of the rule into given context.
		 * 
		 */
		Intp intp( Ctxt const& tgt ) const {
			return Intp(ctxt(),tgt);
		}
		/** @brief instantiates the rule. */
		Thm inst( Intp const& intp ) const {
			return intp.subst(_conclusion);
		}
		bool operator<( Rule const& y ) const {
			return _conclusion < y._conclusion;
		}
	};
	/** @brief Makes a theorem into a rule. */
	static Rule rule( Thm const& thm );
	/** @brief Makes a theorem into an axiom.
	 * universal quantifications are processed but not implications.
     */
	static Rule axiom( Thm const& thm ) {
		return Rule(strip_all(thm));
	}
	Inference( Locale const& loc, CTerm const& claim ) :
		_loc(loc), _thm(_make_claim(claim)), _goals(1) {
	};
	Locale const& locale() const& {
		return _loc;
	}
	Thm thm() const {
		return _thm;
	}
	bool ready() const {
		return _goals == 0;
	}
	size_t goal_count() const {
		return _goals;
	}
	Opt<CTerm> goal() const& {
		if( _goals != 0 ) {
			auto imp = _thm.cbinary(IMP);
			assert(imp);
			return imp->first;
		}
		return {};
	}
	Opt<Thm> concluding() const& {
		if( _goals == 0 ) return _thm;
		return {};
	}
	void discharge( Thm const& thm );
	/** @brief Tries to apply a rule once */
	bool apply( Rule const& rule ) &;
	/** @brief Tries to apply a set of rules once */
	bool apply( std::set<Rule> const& rules ) &;
	/** @brief Applies set of rules many times */
	void apply( std::set<Rule> const& rules, size_t min, size_t max, bool safe ) &;
	void blast( std::set<Rule> const& rules, size_t& fuel ) &;
};

#endif