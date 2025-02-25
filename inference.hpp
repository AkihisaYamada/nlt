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
	/** name for introduction rules */
	static std::string const INTRO;
	/** name for schematic concluders */
	static std::string const CONCL;
	/** name for exact concluder */
	static std::string const EXACT;
	/** Inference rule */
	class Rule {
		friend Inference;
		Thm _conclusion;
	public:
		explicit Rule( Thm const& conc ) : _conclusion(conc) {}
		Thm const& conclusion() const& {
			return _conclusion;
		}
		Thm thm() const& {
			return _conclusion.intro();
		}
		Opt<CSubst> matches( CTerm const& goal ) const {
			return match( _conclusion, goal, [&](auto v){ return ctxt().fixes(v); } );
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
	static Error const NoGoal;
	static Error const Unapplicable;
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
		assert( claim.ctxt() == loc );
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
	Opt<CTerm> has_goal() const& {
		if( _goals != 0 ) {
			auto imp = _thm.cbinary(IMP);
			assert(imp);
			return imp->first;
		}
		return {};
	}
	CTerm goal() const& {
		if( _goals == 0 ) throw NoGoal;
		auto imp = _thm.cbinary(IMP);
		assert(imp);
		return imp->first;
	}
	Opt<Thm> concluding() const& {
		if( _goals == 0 ) return _thm;
		return {};
	}
	/** @brief Tries to apply a rule once */
	void apply( Rule const& rule ) & {
		auto g = goal().weaken(_thm.ctxt().branch());
		if( !_apply(rule,g) ) throw Unapplicable(g);
	}
	/** @brief Tries to apply a set of rules once */
	void apply( std::set<Rule> const& rules ) & {
		auto g = goal().weaken(_thm.ctxt().branch());
		if( !_apply(rules,g) ) throw Unapplicable(g);
	}
	/** @brief Applies set of rules many times */
	void apply( std::set<Rule> const& rules, size_t min, size_t max, bool safe ) &;
	/** @brief Discharge goal by identical theorem */
	void discharge( Thm const& thm ) & {
		if( _goals == 0 ) throw NoGoal;
		if( !_discharges(thm) ) throw Error("\"not exact\"")(thm);
	}
	void blast( std::set<Rule> const& rules, size_t& fuel ) &;
private:
	bool _discharges( Thm const& thm ) & {
		if( auto o = _thm.impEs(thm) ) {
			_thm = *o;
			_goals--;
			return true;
		}
		return false;
	}
	/** goal must be in a fresh context */
	bool _apply( Rule const& rule, CTerm const& goal ) &;
	bool _apply( std::set<Rule> const& rules, CTerm const& goal ) & {
		for( auto const& rule : rules ) {
			if( _apply(rule,goal) ) return true;
		}
		return false;
	}
};

/** @brief Add concluder theorem to locale */
void add_concluder( Locale&, Thm const& thm );

#endif