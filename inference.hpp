#ifndef _INFERENCE_HPP
#define _INFERENCE_HPP

#include "locale.hpp"

/** @brief Add concluder theorem to locale */
void add_concluder( Locale&, Thm const& thm );

/** Class for inference */
class Inference {
	Locale _loc;
	Thm _thm;
	CTerm _claim;
	size_t _goals;
	Inference( Locale const& loc, Thm const& thesis, CTerm const& claim, size_t goals ) :
		_loc(loc), _thm(thesis), _claim(claim), _goals(goals) {}
public:
	/** name for introduction rules */
	static std::string const INTRO;
	/** name for schematic concluders */
	static std::string const CONCL;
	/** name for exact concluder */
	static std::string const EXACT;
	/** name for elimination rules */
	static std::string const ELIM;
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
	static Rule just( Thm const& thm ) {
		return Rule(thm.weaken(thm.ctxt().branch()));
	}
	/** @brief Makes implication a rule. */
	static Rule imp( Thm const& thm );
	/** @brief Makes a theorem into a rule. */
	static Rule rule( Thm const& thm );
	/** @brief Makes a theorem into an axiom.
	 * universal quantifications are processed but not implications.
     */
	static Rule axiom( Thm const& thm ) {
		return Rule(strip_all(thm));
	}
	static Inference claim_exact( Locale const& loc, CTerm const& claim ) {
		Ctxt ctxt = claim.ctxt().branch();
		return Inference( loc, ctxt.assume(claim.weaken(ctxt)).intro(), claim, 1 );// claim ⟹ claim
	}
	static Inference claim_strip( Locale const& loc, CTerm const& claim ) {
		Locale subloc = loc.branch();
		CTerm goal = claim.weaken(subloc);
		goal = strip_all(goal,subloc);
		while( auto imp = goal.cbinary(IMP) ) {
			add_concluder(subloc,subloc.assume(imp->first));
			goal = imp->second;
		}
		return claim_exact(subloc,goal);
	}
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
		auto g = strip_all(goal());
		if( !_apply(rule,g) ) throw Unapplicable(g)(rule.conclusion());
	}
	/** @brief Tries to apply a set of rules once */
	void apply( std::set<Rule> const& rules ) & {
		auto g = strip_all(goal());
		if( !_apply(rules,g) ) throw Unapplicable(g);
	}
	/** @brief Applies set of rules many times */
	void apply( std::set<Rule> const& rules, size_t min, size_t max, bool safe, bool deep ) & {
		size_t suc = 0;
		_apply(rules,suc,min,max,safe,deep);
	}
	void _apply( std::set<Rule> const& rules, size_t& suc, size_t min, size_t max, bool safe, bool deep ) &;
	/** @brief Discharge goal by identical theorem */
	void discharge( Thm const& thm ) & {
		if( _goals == 0 ) throw NoGoal;
		if( !_discharges(thm) ) throw Error("\"not exact\"")(thm);
	}
	void blast( std::set<Rule> const& rules, size_t& fuel ) &;
	/** @brief pushes the top subgoal into assumption.
	 * @return false if there will be no further subgoal */
	bool push() & {
		if( _goals < 2 ) return false;
		_loc = _loc.branch();
		auto assm = _loc.assume(goal().weaken(_loc));
		add_concluder(_loc,assm);
		_thm = _thm.weaken(_loc).impE(assm);
		_goals--;
		return true;
	}
	void pop() & {
		auto p = _loc.parent();
		assert(p);
		_loc = *p;
		_thm = _thm.intro();
		_goals++;
	}

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

/**
 * @brief Blasts first assumption of implication.
 * 
 * @param loc the locale which tells blast the lemmas to use
 * @return Thm the conclusion
 */
Opt<Thm> blasts( Thm const& thesis, Locale const& loc, std::set<Inference::Rule> const& rules = {} );
inline Thm blast( Thm const& thesis, Locale const& loc, std::set<Inference::Rule> const& rules = {} ) {
	auto opt = blasts(thesis,loc,rules);
	assert(opt);
	return *opt;
}

Thm prove( CTerm const& claim, Locale const& loc, std::set<Inference::Rule> const& rules = {} );


#endif