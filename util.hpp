#ifndef _UTIL_HPP_
#define _UTIL_HPP_

#include<list>
#include"core.hpp"

/**
 * @brief forall introduction.
 * 
 * @param thm 
 * @param var 
 * @return Thm 
 */
Thm allI(Thm const& thm, String const& var);

/**
 * @brief renames a variable so that it is fresh in the context.
 * 
 * @param str 
 * @param ctxt 
 * @return the stripped theorem
 */
String make_fresh(std::string const& str, Ctxt const& ctxt);

/**
 * @brief strips universal quantifiers.
 * @param thm the theorem to be stripped.
 * @param loc this context will fix the bound variables.
 */
void strip_all(Thm& thm, Ctxt& loc);
/**
 * @brief strips universal quantifiers.
 * @param t 
 * @param loc this context will fix the bound variables.
 */
void strip_all(Term& t, Ctxt const& loc);

/**
 * @brief Matching, assuming disjoint free variables.
 * @param fsyms the list of free variables
 * @param pat 
 * @param val 
 */
bool match(std::list<String> const& fsyms, Term const& pat, Term const& val, TermMap& subst);

/**
 * @brief Unification.
 * 
 * @param ctxt should fix all the free variables in l and r.
 * @param l 
 * @param r 
 * @param fsyms list of free variables.
 * @param subst should be initially empty.
 * @return true: subst should be a (most general) unifier.
 * @return false: l and r do not unify.
 */
bool unify(Ctxt const& ctxt, Term const& l, Term const& r, std::list<String> const& fsyms, TermMap& subst);

/**
 * @brief Automatically instantiate universally quantified variables so that implication premises are discharged.
 * 
 * @param t 
 * @param arg
 * @return the resulting theorem.
 */
Thm discharge(Thm t, Thm arg);

#endif