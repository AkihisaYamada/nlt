#ifndef _UTIL_HPP_
#define _UTIL_HPP_

#include<list>
#include<ostream>
#include"core.hpp"
#include"graph.hpp"

#define DEB(expr) do { std::cerr << __FILE__ << ":" << __LINE__ << ": " << expr << endl; } while(0)

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
std::optional<CSubst> match(StrSet const& fsyms, CTerm const& pat, CTerm const& val);

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

class Concluder {
	struct Rule {
		CTerm pat;
		Thm thm;
	};
	std::vector<Rule> rules;
public:
	void insert(Thm const& thm) {
		Ctxt loc = thm.ctxt().branch();
		Thm pat = strip_all(thm,loc);
		rules.push_back({pat,thm});
	}
	Thm conclude(Thm const& target);
};

/**
 * @brief Congruence prover.
 * 
 */
class Rewriter {
	struct Rule {
		CTerm pat;
		Thm thm;
	};
	std::vector<Rule> congs;
	std::vector<Rule> quantifier_congs;
public:
	Thm const refl, sym, trans, imp;
	struct Error : std::exception {
		Term term;
		Error(Term const& term) : term(term) {}
	};
	struct TooFewSteps : std::exception {
		Term term;
		TooFewSteps(Term const& term) : term(term) {}
	};
	struct TooManySteps : std::exception {
		Term term;
		TooManySteps(Term const& term) : term(term) {}
	};
	class Rules : std::vector<Rule> {
	public:
		Rules() {}
		Rules& add(Thm const& thm);
		friend Rewriter;
	};
	Rewriter(Thm const& refl, Thm const& sym, Thm const& trans, Thm const& imp) :
		refl(refl), sym(sym), trans(trans), imp(imp) {}
	Thm reverse(Thm const& thm) const {
		return discharge(sym.weaken(thm.ctxt()),thm);
	}
	void register_cong(CTerm const& pat, Thm const& rule) {
		congs.push_back({pat,rule});
	}
	void register_quantifier_cong(CTerm const& pat, Thm const& rule) {
		quantifier_congs.push_back({pat,rule});
	}
	void register_concl(Thm const& rule);
	/**
	 * @brief returns a rewrite step equation for the given source term.
	 * 
	 * @param source the term to be rewritten
	 * @return std::optional<Thm> 
	 */
	std::optional<Thm> step(Rules const& rules, CTerm const& source) const {
		return _step(rules,source,refl.weaken(source.ctxt()));
	}
	/**
	 * @brief returns a rewrite step equation for the given source term at given position.
	 * 
	 * @param source the term to be rewritten
	 * @return std::optional<Thm> 
	 */
	std::optional<Thm> step(Rules const& rules, CTerm const& source, std::vector<char> const& pos) const {
		return _step(rules,source,pos.begin(),pos.end(),refl.weaken(source.ctxt()));
	}
	/**
	 * @brief many step rewrite equation
	 * 
	 * @param rules 
	 * @param source 
	 * @param n 
	 * @param pos 
	 * @return Thm 
	 */
	Thm steps(Rules const& rules, CTerm const& source, unsigned int min, unsigned int max, std::vector<char> const& pos) const;
	Thm rewrite(Rules const& rules, Thm const& source, unsigned int min, unsigned int max, std::vector<char> const& pos) const;
private:
	std::optional<Thm> congruence(std::function<std::optional<Thm>(CTerm const&)> inner, CTerm const& source) const;
	std::optional<Thm> _step(Rules const& rules, CTerm const& source, Thm const& refl) const;
	std::optional<Thm> _step( Rules const& rules, CTerm const& haystack, std::vector<char>::const_iterator it, std::vector<char>::const_iterator end, Thm const& refl ) const;
	friend std::ostream& operator<<( std::ostream& os, Rule const& rule );
};

inline std::ostream& operator<<( std::ostream& os, Rewriter::Rule const& rule ) {
	return os << '[' << rule.pat << "] " << rule.thm;
}

class Definer {
	Ptr<Rewriter const> rewriter;
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
	void define(Ctxt& ctxt, Term const& l, Term const& r, std::optional<String> const& name) const;
};

#endif