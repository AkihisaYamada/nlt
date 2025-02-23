#ifndef _UTIL_HPP_
#define _UTIL_HPP_

#include<ostream>
#include"syntax.hpp"

#define INTRO "#intro"// name for introduction rules
#define ASSM "#assm"// name for assumptions

inline std::string operator+( std::string x, std::string_view const& y ) {
	x+=y;
	return x;
}

extern Term const DUMMY;

/** comparison of terms */
int compare_term( Term const& l, Term const& r );
/** comparison of terms */
bool operator<( Term const& l, Term const& r );

/** makes the theorem t ⟹ t */
inline Thm make_refl( CTerm const& t ) {
	Ctxt ctxt = t.ctxt().branch();
	return ctxt.assume(t.weaken(ctxt)).intro();
}

/** Iterate over locally fixed variables. */
inline void iter_local_vars( Ctxt const& ctxt, std::function<void(std::string const&)> f ) {
	for( size_t i = 0; i < ctxt.revision(); i++ ) {
		if( auto const& fix = ctxt.fixed(i) ) {
			f(*fix);
		}
	}
}

using Renamer = std::function<Opt<std::string>(std::string_view const&)>;

/**
 * @brief default renamer.
 * 
 * @param ctxt 
 * @return function that always gives a fresh name in the context.
 */
Renamer avoider(Ctxt& ctxt);

/** Fresh variable maker */
Renamer fresh_maker();

/**
 * @brief strips universal quantifiers.
 * @param t 
 * @param ctxt this context will fix the bound variables.
 * @param renamer
 */
CTerm strip_all( CTerm t, Ctxt& ctxt, Renamer const& renamer );

/**
 * @brief strips universal quantifiers with default renaming
 */
inline CTerm strip_all(CTerm t, Ctxt& ctxt) {
	return strip_all(t,ctxt,avoider(ctxt));
}

/**
 * @brief strips universal quantifiers.
 * @param thm the theorem to be stripped.
 * @param loc this context will fix the bound variables.
 */
Thm strip_all( Thm thm, Ctxt& ctxt, Renamer const& renamer );
inline Thm strip_all( Thm thm, Ctxt& ctxt ) {
	return strip_all(thm,ctxt,avoider(ctxt));
}
inline Thm strip_all( Thm thm ) {
	Ctxt ctxt = thm.ctxt().branch();
	return strip_all(thm,ctxt);
}

/**  */
class Rule {
	Thm _conclusion;
	Rule( Thm const& conc ) : _conclusion(conc) {}
public:
	/** @brief Makes a theorem into a rule. */
	static Rule make( Thm const& thm );
	/** @brief Makes a theorem into an axiom.
	 * universal quantifications are processed but not implications.
     */
	static Rule axiom( Thm const& thm ) {
		return Rule(strip_all(thm));
	}
	std::function<bool(std::string_view const& v)> const fvars = [&](auto v){ return ctxt().fixes(v); };
	Thm const& conclusion() const& {
		return _conclusion;
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

class Thesis {
	Locale _loc;
	Thm _thm;
	size_t _goals;
	static Thm _make_claim( CTerm const& claim ) {
		Ctxt ctxt = claim.ctxt().branch();
		return ctxt.assume(claim.weaken(ctxt)).intro();// claim ⟹ claim
	}
public:
	Thesis( Locale const& loc, CTerm const& claim ) :
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
	bool blast( std::set<Rule> const& rules, size_t& fuel ) &;
};


/** @brief 
 * @param imp ∀x... φ ⟹ ψ
 * @param arg φθ
 * @return ∀y... ψθ
 */
Opt<Thm> match_discharge( Thm const& imp, Thm const& arg );

/**
 * @brief Uncurrying
 * 
 * @param t 
 * @return std::pair<std::string,std::vector<Term>> 
 */
std::pair<std::string,std::list<Term>> uncurry(Term const& t);

/**
 * @brief Strip binary operator
 * 
 * @param t 
 * @return std::tuple<std::string,CTerm,CTerm> 
 */
Opt<std::tuple<std::string,CTerm,CTerm>> strips_binary(CTerm const& t);

/**
 * @brief Matching, assuming disjoint free variables.
 * @param pat 
 * @param val 
 * @param fvar signifies free variables.
 */
Opt<CSubst> match( CTerm const& pat, CTerm const& val, std::function<bool(std::string_view const&)> const& fvar );

/**
 * @brief Unification.
 * The input two terms must be closed with respect to a context.
 * @param l 
 * @param r 
 * @param fvar signifies free variables.
 * @return an idempotent, most general unifier iff `l` and `r` are unifiable.
 */
Opt<CSubst> unify(CTerm const& l, CTerm const& r, std::function<bool(std::string const&)> const& fvar);

/**
 * @brief Automatically instantiate universally quantified variables so that implication premises are discharged.
 * 
 * @param t 
 * @param arg
 * @return the resulting theorem.
 */
Thm discharge(Thm t, Thm arg);

/** Discharge */
inline Thm operator<<(Thm const& t, Thm arg) {
	return discharge(t,arg);
}

/** detects trivial abstraction x. y.[x], and returns y */
Opt<std::string> virtual_var( CTerm const& t );

#endif