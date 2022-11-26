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
 * @param t 
 * @param loc this context will fix the bound variables.
 */
Term strip_all(Term t, Ctxt& loc);
/**
 * @brief strips universal quantifiers.
 * @param t 
 * @param loc this context will fix the bound variables.
 */
CTerm strip_all(CTerm t, Ctxt& loc);
/**
 * @brief strips universal quantifiers.
 * @param thm the theorem to be stripped.
 * @param loc this context will fix the bound variables.
 */
Thm strip_all(Thm thm, Ctxt& loc);

/**
 * @brief Uncurrying
 * 
 * @param t 
 * @return std::pair<String,std::vector<Term>> 
 */
std::pair<String,std::list<Term>> uncurry(Term const& t);

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

/**
 * @brief Imports a context into the parent
 * 
 * @param ctxt 
 * @param target 
 */
void import(Ctxt ctxt, Ctxt const& target);

/**
 * @brief Congruence prover.
 * 
 */
class Rewriter {
	struct Rule {
		Thm thm;
		CTerm pat;
	};
public:
	Thm const cong, fun_cong, arg_cong, ext, eq_imp, refl, trans;
	struct Error : std::exception {
		Term term;
		Error(Term const& term) : term(term) {}
	};
	class Rules : std::vector<Rule> {
	public:
		Rules() {}
		Rules& add(Thm const& thm);
		friend Rewriter;
	};
	Rewriter(StrMap<Thm> const& args) :
		cong(args.at("cong")),fun_cong(args.at("fun_cong")),arg_cong(args.at("arg_cong")),
		ext(args.at("ext")),eq_imp(args.at("eq_imp")),refl(args.at("refl")),trans(args.at("trans")) {}
	/**
	 * @brief returns a rewrite step equation for the given left hand side.
	 * 
	 * @param haystack the left hand side
	 * @return std::optional<Thm> 
	 */
	std::optional<Thm> equate(Rules const& rules, CTerm const& haystack) const;
	/**
	 * @brief rewrites a theorem one step.
	 */
	std::optional<Thm> rewrite(Rules const& rules, Thm const& thm) const;
	/**
	 * @brief normalizes a theorem.
	 * 
	 * @param rules 
	 * @param thm 
	 * @param steps limits the number of steps
	 * @return the normal form
	 */
	Thm normalize(Rules const& rules, Thm const& thm, unsigned int steps) const;
};

class Definer {
	Ref<Rewriter const> rewriter;
	String const EQ;
	Term const LAM;
	Rewriter::Rules beta;
public:
	struct Error : std::exception {
		Term term;
		Error(Term const& term) : term(term) {}
	};
	Definer(Rewriter const& rewriter, String const& EQ, Term const& LAM, Thm const& beta) :
		rewriter(rewriter), LAM(LAM), EQ(EQ)
	{
		this->beta.add(beta);
	}
	void define(Ctxt& ctxt, Term const& rule, std::optional<String const> sym) const;
};

#endif