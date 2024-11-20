#ifndef _UTIL_HPP_
#define _UTIL_HPP_

#include<ostream>
#include"syntax.hpp"

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

/**
 * @brief strips universal quantifiers.
 * @param t 
 * @param loc this context will fix the bound variables.
 */
Term strip_all(Term t, Ctxt& loc);

using Renamer = std::function<Opt<std::string>(std::string_view const&)>;

/**
 * @brief default renamer.
 * 
 * @param ctxt 
 * @return function that always gives a fresh name in the context.
 */
Renamer avoider(Ctxt& ctxt);

/**
 * @brief strips universal quantifiers.
 * @param t 
 * @param ctxt this context will fix the bound variables.
 * @param renamer
 */
CTerm strip_all(CTerm t, Ctxt& ctxt, Renamer const& renamer );

/**
 * @brief 
 * 
 * @param t 
 * @param ctxt 
 * @return CTerm 
 */
inline CTerm strip_all(CTerm t, Ctxt& ctxt) {
	return strip_all(t,ctxt,avoider(ctxt));
}

/**
 * @brief strips universal quantifiers.
 * @param thm the theorem to be stripped.
 * @param loc this context will fix the bound variables.
 */
Thm strip_all(Thm thm, Ctxt& loc);

/** @brief Makes a theorem into the conclusion, whose context contains the conditions. */
Thm make_rule( Thm const& thm );

/** @brief Applies an inference rule */
Opt<Thm> rule_applies( Thm const& rule, Thm const& thesis );

/** @brief Applies one of inference rules */
Opt<Thm> rules_apply( std::set<Thm> const& rules, Thm const& thesis );

/**
 * @brief Uncurrying
 * 
 * @param t 
 * @return std::pair<std::string,std::vector<Term>> 
 */
std::pair<std::string,std::list<Term>> uncurry(Term const& t);

/**
 * @brief Matching, assuming disjoint free variables.
 * @param fsyms the set of free variables
 * @param pat 
 * @param val 
 */
Opt<CSubst> match(StrSet const& fsyms, CTerm const& pat, CTerm const& val);

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