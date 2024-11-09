#ifndef _REWRITER_HPP_
#define _REWRITER_HPP_

#include "util.hpp"

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
	/** ∀x. x = x */
	Thm const refl;
	/** ∀x y. x = y ⟹ y = x */
	Thm const sym;
	/** ∀x y z. x = y ⟹ y = z ⟹ x = z */
	Thm const trans;
	/** ∀x y. (x = y) ⟹ x ⟹ y */
	Thm const imp;
	struct Error : ::Error {
		static inline Term const RT = "#rewriter";
		Error(Term const& term) : ::Error(RT(term)) {}
	};
	struct TooFewSteps : Error {
		static inline Term const RT = "#too_few_steps";
		TooFewSteps(size_t a, size_t e, Term const& term) :
			Error(RT(std::to_string(a))(std::to_string(e))(term)) {}
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
		quantifier_congs.emplace_back(pat,rule);
	}
	void register_concl(Thm const& rule);
	/**
	 * @brief returns a rewrite step equation for the given source term.
	 * 
	 * @param source the term to be rewritten
	 * @return Opt<Thm> 
	 */
	Opt<Thm> step(Rules const& rules, CTerm const& source) const {
		return _step(rules,source,refl.weaken(source.ctxt()));
	}
	/**
	 * @brief returns a rewrite step equation for the given source term at given position.
	 * 
	 * @param source the term to be rewritten
	 * @return Opt<Thm> 
	 */
	Opt<Thm> step(Rules const& rules, CTerm const& source, std::vector<char> const& pos) const {
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
	Opt<Thm> congruence(std::function<Opt<Thm>(CTerm const&)> inner, CTerm const& source) const;
	Opt<Thm> _step(Rules const& rules, CTerm const& source, Thm const& refl) const;
	Opt<Thm> _step( Rules const& rules, CTerm const& haystack, std::vector<char>::const_iterator it, std::vector<char>::const_iterator end, Thm const& refl ) const;
	friend std::ostream& operator<<( std::ostream& os, Rule const& rule );
};

inline std::ostream& operator<<( std::ostream& os, Rewriter::Rule const& rule ) {
	return os << '[' << rule.pat << "] " << rule.thm;
}
#endif
