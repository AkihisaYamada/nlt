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
	struct Cong : Thm {
		CTerm pat;
		std::vector<size_t> inds;
		std::vector<bool> abss;
		Cong( CTerm const& pat, Thm const& thm, std::vector<size_t> && inds, std::vector<bool> && abss ) : pat(pat), Thm(thm), inds(std::move(inds)), abss(std::move(abss)) {}
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
	Map<size_t,Thm> _trans;
	/** ∀P Q. P ⟺ Q ⟹ P ⟹ Q */
	Map<size_t,Thm> _imps;
public:
	struct Error : ::Error {
		static inline Term const RT = "#rewriter";
		Error(Term const& term) : ::Error(RT(term)) {}
	};
	static Error const UnregisteredRel;
	static Error const MalformedImp;
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
	Opt<size_t> gets_rel_ind( std::string_view const& rel ) const {
		if( auto const& ind = _rels.finds(rel) ) {
			return ind->second;
		}
		return {};
	}
	Thm get_refl( size_t ind ) const {
		assert( ind < _refls.size() );
		return _refls[ind];
	}
	void add_rule( Rules& rules, Thm const& thm, bool rev = false ) const;
	void register_imp(Thm const& thm);
	void register_refl(Thm const& thm);
	void register_trans(Thm const& thm);
	void register_cong(Thm const& thm);
	void register_dual(Thm const& thm);
	/**
	 * @brief returns a rewrite step equation for the given source term.
	 * 
	 * @param source the term to be rewritten
	 * @return Opt<Thm> 
	 */
	Opt<Thm> step( Rules const& rules, CTerm const& source, size_t ind = 0 ) const {
		return _step(rules,source,ind);
	}
	/**
	 * @brief returns a rewrite step equation for the given source term at given position.
	 * 
	 * @param source the term to be rewritten
	 * @return Opt<Thm> 
	 */
	Opt<Thm> step( Rules const& rules, CTerm const& source, std::vector<char> const& pos, size_t ind = 0 ) const {
		return _step(rules,source,ind,pos.begin(),pos.end());
	}
	/**
	 * @brief many step rewrite equation
	 * 
	 * @param rules 
	 * @param source 
	 * @param n 
	 * @param pos 
	 * @param rel the relation symbol, e.g., "="
	 * @return Thm 
	 */
	Thm steps( Rules const& rules, CTerm const& source, unsigned int min, unsigned int max, bool safe, std::vector<char> const& pos, std::string_view const& rel ) const {
		auto ind = gets_rel_ind(rel);
		if( !ind ) {
			throw UnregisteredRel(rel);
		}
		return _steps(rules,source,min,max,safe,pos,*ind);
	}
	/** @brief Rewrites a theorem
	 */
	Thm rewrite( Rules const& rules, Thm const& source, unsigned int min, unsigned int max, bool safe, std::vector<char> const& pos, Opt<std::string> const& rel = {} ) const {
		size_t ind = rel ? [&]{
			auto const& o = gets_rel_ind(*rel);
			if( !o ) throw UnregisteredRel(*rel);
			return *o;
		}() : 0;
		return _rewrite(rules,source,min,max,safe,pos,ind);
	}
private:
	Opt<Thm> _step( Rules const& rules, CTerm const& source, size_t ind ) const;
	Opt<Thm> _step_abs( Rules const& rules, CTerm const& source, size_t ind ) const;
	Opt<Thm> _step( Rules const& rules, CTerm const& source, size_t ind, std::vector<char>::const_iterator it, std::vector<char>::const_iterator end ) const;
	Opt<Thm> _step_abs( Rules const& rules, CTerm const& source, size_t ind, std::vector<char>::const_iterator it, std::vector<char>::const_iterator end ) const;
	Thm _steps( Rules const& rules, CTerm const& source, unsigned int min, unsigned int max, bool safe, std::vector<char> const& pos, size_t ind ) const;
	Thm _rewrite( Rules const& rules, Thm const& source, unsigned int min, unsigned int max, bool safe, std::vector<char> const& pos, size_t ind ) const;
	friend std::ostream& operator<<( std::ostream& os, Rule const& rule );
};

inline std::ostream& operator<<( std::ostream& os, Rewriter::Rule const& rule ) {
	return os << '[' << rule.pat << "] " << rule.thm;
}
#endif
