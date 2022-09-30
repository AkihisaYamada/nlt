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
class Rewriter : public ThmTransformer {
	static CTerm rule2pat(Thm const& thm);
	static String BOX;
	Thm EQ_mono;
	struct Rule {
		Thm thm;
		CTerm pat;
		Rule(Thm const& thm) : thm(thm), pat(rule2pat(thm)) {}
	};
	std::vector<Rule> rules;
	std::optional<Thm> apply(Thm const& thm, CTerm const& context, CTerm const& haystack) const;
public:
	Rewriter(Thm const& EQ_mono) : EQ_mono(EQ_mono) {}
	Rewriter& add(Thm const& thm) {
		rules.push_back(thm);
		return *this;
	}
	std::optional<Thm> apply(Thm const& thm);
};

struct MalformedRewrite : std::exception {
	Term term;
	MalformedRewrite(Term const& term) : term(term) {}
};

#endif