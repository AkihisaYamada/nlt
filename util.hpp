#ifndef _UTIL_HPP_
#define _UTIL_HPP_

#include<list>
#include<ostream>
#include"core.hpp"
#include"graph.hpp"

std::ostream& operator<<(std::ostream& os, Term const& t);
std::ostream& operator<<(std::ostream& os, CSubst const& subst);


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
 * @param fsyms the set of free variables
 * @param pat 
 * @param val 
 */
std::optional<CSubst> match(Syms const& fsyms, CTerm const& pat, CTerm const& val);

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
 * The input two terms must be closed with respect to a context.
 * @param l 
 * @param r 
 * @param fvar signifies free variables.
 * @return an idempotent, most general unifier iff `l` and `r` are unifiable.
 */
std::optional<CSubst> unify(CTerm const& l, CTerm const& r, std::function<bool(String const&)> const& fvar);

/**
 * @brief Automatically instantiate universally quantified variables so that implication premises are discharged.
 * 
 * @param t 
 * @param arg
 * @return the resulting theorem.
 */
Thm discharge(Thm t, Thm arg);

class ThmTransformer {
	virtual std::optional<Thm> apply(Thm const& thm) = 0;
};
/**
 * @brief Congruence prover.
 * 
 */
namespace Rewrite {
	struct Axioms {
		Thm cong, fun_cong, arg_cong, ext, refl, trans;
		Axioms(StrMap<Thm> const& args) :
			cong(args.at("cong")),fun_cong(args.at("fun_cong")),arg_cong(args.at("arg_cong")),
			ext(args.at("ext")),refl(args.at("refl")),trans(args.at("trans")) {}
	};
	struct Rule {
		Thm thm;
		CTerm pat;
	};
	class Rules : std::vector<Rule> {
		Axioms axioms;
		Thm _rewrite(CTerm const& haystack) const;
	public:
		Rules& add(Thm const& thm);
		Rules(Axioms const& axioms) : axioms(axioms) {}
		std::optional<Thm> rewrite(CTerm const& haystack) const;
	};
	struct Error : std::exception {
		Term term;
		Error(Term const& term) : term(term) {}
	};
};

#endif