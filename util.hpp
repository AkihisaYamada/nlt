#ifndef _UTIL_HPP_
#define _UTIL_HPP_

#include<list>
#include<ostream>
#include"core.hpp"
#include"graph.hpp"

std::ostream& operator<<(std::ostream& os, Term const& t);

/**
 * @brief strips universal quantifiers.
 * @param thm the theorem to be stripped.
 * @param loc this context will fix the bound variables.
 */
Thm strip_all(Thm thm, Ctxt& loc);
/**
 * @brief strips universal quantifiers.
 * @param t 
 * @param loc this context will fix the bound variables.
 */
CTerm strip_all(CTerm t, Ctxt& loc);

/**
 * @brief Matching, assuming disjoint free variables.
 * @param fsyms the list of free variables
 * @param pat 
 * @param val 
 */
bool match(std::list<String> const& fsyms, Term const& pat, Term const& val, StrMap<Term>& subst);

class SubstDag : public CSubst, public Graph<String,std::less<>> {
public:
	struct Cyclic : std::exception {};
	/**
	 * @brief assigns a variable a value, while maintaining acyclicity
	 * 
	 * @param var 
	 * @param val 
	 */
	void assign(String const& var, CTerm const& val) {
		if( val != var ) {
			CSubst::assign(var,val);
			val.iter_syms([](auto){},
				[&](String const& sym) {
					if( has_path(sym,var) ) {
						throw Cyclic();
					}
					add_edge(var,sym);
				}
			);
		}
	}
	void close() {
		for( auto const& p : map() ) {
			CSubst::assign(p.first,get(p.first)->subst(*this));
		}
	}
};

/**
 * @brief Unification.
 * The input two terms must be closed with respect to a context. Local symbols of the context will be considered to be free variables.
 * @param l 
 * @param r 
 * @return an idempotent, most general unifier iff `l` and `r` are unifiable.
 */
std::optional<CSubst> unify(CTerm const& l, CTerm const& r);

/**
 * @brief Automatically instantiate universally quantified variables so that implication premises are discharged.
 * 
 * @param t 
 * @param arg
 * @return the resulting theorem.
 */
Thm discharge(Thm t, Thm arg);

#endif