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
 * @param ctxt 
 * @param orig 
 * @param fsyms the list of avoided free variables. The quantified variables will be appended.
 * @return the stripped theorem
 */
String make_fresh(std::list<String> const& syms, Ctxt const& ctxt, String const& orig);

/**
 * @brief strips universal quantifiers.
 * @param fsyms list of free variables.
 * @param thm 
 * @return the stripped theorem.
 */
Thm strip_all(std::list<String>& fsyms, Thm thm);
/**
 * @brief strips universal quantifiers.
 * @param fsyms list of free variables.
 * @param ctxt the context which `t` term belongs to.
 * @param t 
 * @return the stripped term.
 */
Term strip_all(std::list<String>& fsyms, Ctxt const& ctxt, Term const& t);

/**
 * @brief Matching, assuming disjoint free variables.
 * @param fsyms the list of free variables
 * @param pat 
 * @param val 
 */
bool match(std::list<String> const& fsyms, Term const& pat, Term const& val, TermMap& subst);

/**
 * @brief Automatically instantiate universally quantified variables so that implication premises are discharged.
 * 
 * @param t 
 * @param args 
 * @return the resulting theorem.
 */
Thm inst_discharge(Thm t, std::list<Thm> args);

#endif