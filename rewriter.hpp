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
	struct Cong {
		CTerm pat;
		Thm thm;
		std::vector<size_t> inds;
		Cong( CTerm const& pat, Thm const& thm, std::vector<size_t> && inds ) :
			pat(pat), thm(thm), inds(std::move(inds)) {}
	};
	struct Dual {
		Thm thm;
		size_t ind;
	};
	std::vector<std::vector<Cong>> _congs;
	/** relation symbols, e.g., ⟺ or = */
	StrMap<size_t const> _rels;
	/** reflexivity theorems, e.g., ∀x. x = x */
	std::vector<Thm> _refls;
	/** symmetry theorems, e.g., ∀x y. x = y ⟹ y = x */
	Map<size_t,Dual> _duals;
	/** ∀x y z. x = y ⟹ y = z ⟹ x = z */
	std::vector<Thm> _trans;
public:
	struct Error : ::Error {
		static inline Term const RT = "#rewriter";
		Error(Term const& term) : ::Error(RT(term)) {}
	};
	class Rules : std::vector<std::vector<Rule>> {
		Rules( size_t n ) : std::vector<std::vector<Rule>>(n) {}
		friend Rewriter;
	};
	struct TooFewSteps : Error {
		static inline Term const RT = "#too_few_steps";
		TooFewSteps(size_t a, size_t e, Term const& term) :
			Error(RT(std::to_string(a))(std::to_string(e))(term)) {}
	};
	Rules make_rules() const {
		return Rules(_rels.size());
	}
	Opt<size_t> gets_rel_ind( std::string const& rel ) const {
		if( auto const& ind = _rels.finds(rel) ) {
			return ind->second;
		}
		return {};
	}
	Thm get_refl( size_t ind ) const {
		return _refls[ind];
	}
	void add_rule( Rules& rules, Thm const& thm, bool rev = false ) const;
	/** ∀x y. (x = y) ⟹ x ⟹ y */
	Thm const imp;
	Rewriter(Thm const& refl, Thm const& trans, Thm const& imp) : imp(imp) {
		register_refl(refl);
		_trans.emplace_back(trans);
	}
	void register_refl(Thm const& thm);
	void register_cong(Thm const& thm);
	void register_dual(Thm const& thm);
	/**
	 * @brief returns a rewrite step equation for the given source term.
	 * 
	 * @param source the term to be rewritten
	 * @return Opt<Thm> 
	 */
	Opt<Thm> step(Rules const& rules, CTerm const& source) const {
		return _step(rules,source,0);
	}
	/**
	 * @brief returns a rewrite step equation for the given source term at given position.
	 * 
	 * @param source the term to be rewritten
	 * @return Opt<Thm> 
	 */
	Opt<Thm> step(Rules const& rules, CTerm const& source, std::vector<char> const& pos) const {
		return _step(rules,source,0,pos.begin(),pos.end());
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
	Thm steps(Rules const& rules, CTerm const& source, unsigned int min, unsigned int max, bool safe, std::vector<char> const& pos) const;
	Thm rewrite(Rules const& rules, Thm const& source, unsigned int min, unsigned int max, bool safe, std::vector<char> const& pos) const;
private:
	Opt<Thm> _step( Rules const& rules, CTerm const& source, size_t ind ) const;
	Opt<Thm> _step_abs( Rules const& rules, CTerm const& source, size_t ind ) const;
	Opt<Thm> _step( Rules const& rules, CTerm const& source, size_t ind, std::vector<char>::const_iterator it, std::vector<char>::const_iterator end ) const;
	Opt<Thm> _step_abs( Rules const& rules, CTerm const& source, size_t ind, std::vector<char>::const_iterator it, std::vector<char>::const_iterator end ) const;
	friend std::ostream& operator<<( std::ostream& os, Rule const& rule );
};

inline std::ostream& operator<<( std::ostream& os, Rewriter::Rule const& rule ) {
	return os << '[' << rule.pat << "] " << rule.thm;
}
#endif
