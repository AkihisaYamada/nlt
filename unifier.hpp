#ifndef _UNIFIER_HPP_
#define _UNIFIER_HPP_
#include<list>
#include"core.hpp"

/**
 * @brief Unification.
 * 
 * @param ctxt should fix all the free variables in l and r.
 * @param l 
 * @param r 
 * @param fsyms the set of free variables.
 * @param subst should be initially empty.
 * @return true: subst should be a (most general) unifier.
 * @return false: l and r do not unify.
 */
bool unify(Ctxt const& ctxt, Term const& l, Term const& r, Syms& fsyms, TermMap& subst);

#endif