#ifndef _REWRITER_HPP_
#define _REWRITER_HPP_

#include "inference.hpp"

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
		struct Cond {
			size_t ind;
			bool abs;
			CTerm assm;
		};
		CTerm pat;
		std::vector<Cond> conds;
		Cong( CTerm const& pat, Thm const& thm, std::vector<Cond> && conds ) : pat(pat), Thm(thm), conds(std::move(conds)) {}
	};
	struct Dual {
		Thm thm;
		size_t ind;
	};
	struct Imp {
		Thm thm;// s = t ⟹ conditions ... ⟹ s ⟹ t
		size_t conds;// number of conditions
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
	Map<size_t,Imp> _imps;
	/** ∀P Q. P ⟺ Q ⟹ Q ⟹ P */
	Map<size_t,Imp> _revimps;
public:
	static std::string const CONG;
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
	struct Ctrl {
		Opt<std::string> rel;
		std::vector<char> pos;
		size_t min, max;
		bool safe;
	};
	struct TooFewSteps : Error {
		static inline Term const RT = "\"too few steps\"";
		TooFewSteps(size_t a, size_t e, Term const& term) :
			Error(RT(std::to_string(a))(std::to_string(e))(term)) {}
	};
	struct TooManySteps : Error {
		static inline Term const RT = "#too many steps";
		TooManySteps(size_t max, Term const& term) :
			Error(RT(std::to_string(max))(term)) {}
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
	void add_rule( Locale const& loc, Rules& rules, Thm const& thm, bool rev = false ) const;
	void register_imp( Thm const& thm, bool dir );
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
	Opt<Thm> step( Rules const& rules, Locale const& loc, CTerm const& source, size_t ind = 0 ) const {
		return _step(rules,loc,source,ind);
	}
	/**
	 * @brief returns a rewrite step equation for the given source term at given position.
	 * 
	 * @param source the term to be rewritten
	 * @return Opt<Thm> 
	 */
	Opt<Thm> step( Rules const& rules, Locale const& loc, CTerm const& source, std::vector<char> const& pos, size_t ind = 0 ) const {
		return _step(rules,loc,source,ind,pos.begin(),pos.end());
	}
	/** @brief applies rewriting */
	bool apply( Rules const& rules, Inference& thesis, Ctrl const& ctrl ) const;
	/** @brief Rewrites a theorem */
	Thm rewrite( Rules const& rules, Locale const& loc, Thm const& source, Ctrl const& ctrl ) const;
private:
	size_t _get_ind( Opt<std::string> const& rel ) const;
	Opt<Thm> _step( Rules const& rules, Locale const& loc, CTerm const& source, size_t ind ) const;
	Opt<Thm> _step_abs( Rules const& rules, Locale const& loc, CTerm const& source, size_t ind, CTerm const& assm, CSubst const& subst ) const;
	Opt<Thm> _step( Rules const& rules, Locale const& loc, CTerm const& source, size_t ind, std::vector<char>::const_iterator it, std::vector<char>::const_iterator end ) const;
	Opt<Thm> _step_abs( Rules const& rules, Locale const& loc, CTerm const& source, size_t ind, std::vector<char>::const_iterator it, std::vector<char>::const_iterator end ) const;
	Opt<Thm> _steps( Rules const& rules, Locale const& loc, CTerm const& source, size_t min, size_t max, bool safe, std::vector<char> const& pos, size_t ind ) const;
	friend std::ostream& operator<<( std::ostream& os, Rule const& rule );
};

inline std::ostream& operator<<( std::ostream& os, Rewriter::Rule const& rule ) {
	return os << '[' << rule.pat << "] " << rule.thm;
}
#endif
