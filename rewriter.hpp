#ifndef _REWRITER_HPP_
#define _REWRITER_HPP_

#include"util.hpp"

class Thy;

class Inference;
/**
 * @brief Congruence prover.
 * 
 */
class Rewriter {
	struct Rule {
		CTerm pat;// Γ.fix x... assume φ... ⊢ l
		Thm rule;//  Γ.fix x... assume φ... ⊢ l = r
		Ctxt ctxt;// Γ, holding ∀x... φ ⟹... l = r
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
	/** relation symbols, e.g., ⟺ or = */
	std::vector<std::string> _rels;
	StrMap<size_t const> _rel2ind;
	/** reflexivity theorems, e.g., ∀x. x = x */
	std::vector<Thm> _refls;
	/** symmetry theorems, e.g., ∀x y. x = y ⟹ y = x */
	Map<size_t,Dual> _duals;
	/** ∀x y z. x = y ⟹ y = z ⟹ x = z */
	Map<size_t,Thm> _trans;
	/** ∀P Q. P = Q ⟹ P ⟹ Q */
	Map<size_t,Imp> _imps;
	/** ∀P Q. P = Q ⟹ Q ⟹ P */
	Map<size_t,Imp> _revimps;
	/** ∀x y x' y'. x = x' ⟹ y = y' ⟹ x + y = x' + y' */
	std::vector<std::vector<Cong>> _congs;
	/** ∀P. P ⟹ P = true */
	Opt<std::pair<Thm,size_t>> _to_true;
	size_t _default_ind;
public:
	static std::string const CONG;
	struct Error : ::Error {
		static inline Term const RT = "#rewriter";
		Error(Term const& term) : ::Error(RT(term)) {}
	};
	char log;
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
	bool empty() const {
		return _rels.empty();
	}
	Rules make_rules() const {
		return Rules(_rels.size());
	}
	Opt<size_t> gets_rel_ind( std::string_view const& rel ) const {
		if( auto const& ind = _rel2ind.finds(rel) ) {
			return ind->second;
		}
		return {};
	}
	Thm get_refl( size_t ind ) const {
		assert( ind < _refls.size() );
		return _refls[ind];
	}
	void add_rule( Rules& rules, Thm const& thm, Thy const& thy ) const;
	Thm dualize( Thm const& thm, Thy const& thy ) const;
	Rewriter& register_imp( Thm const& thm, bool dir ) &;
	Rewriter& register_refl( Thm const& thm, bool def ) &;
	Rewriter& register_trans( Thm const& thm ) &;
	Rewriter& register_cong( Thm const& thm ) &;
	Rewriter& register_dual( Thm const& thm ) &;
	Rewriter& register_to_true( Thm const& thm ) &;
	/**
	 * @brief returns a rewrite step equation for the given source term.
	 * 
	 * @param source the term to be rewritten
	 * @return Opt<Thm> 
	 */
	Opt<Thm> step( Rules const& rules, Thy const& thy, CTerm const& source ) const {
		return _step(rules,thy,source,_default_ind);
	}
	/**
	 * @brief returns a rewrite step equation for the given source term at given position.
	 * 
	 * @param source the term to be rewritten
	 * @return Opt<Thm> 
	 */
	Opt<Thm> step( Rules const& rules, Thy const& thy, CTerm const& source, std::vector<char> const& pos ) const {
		return _step(rules,thy,source,_default_ind,pos.begin(),pos.end());
	}
	/** @brief applies rewriting */
	bool apply( Rules const& rules, Inference& thesis) const;
	/** @brief applies rewriting with control */
	bool apply( Rules const& rules, Inference& thesis, Ctrl const& ctrl ) const;
	/** @brief Rewrites a theorem */
	Thm rewrite( Thy const& thy, Thm const& source, Rules const& rules, Ctrl const& ctrl ) const;
	/** @brief returns a rewriting theorem */
	Thm steps( Rules const& rules, Thy const& thy, CTerm const& source, Ctrl const& ctrl ) const {
		size_t ind = _get_ind(ctrl.rel);
		if( auto ret = _steps(rules,thy,source,ctrl.min,ctrl.max,ctrl.safe,ctrl.pos,ind) ) {
			return *ret;
		}
		return _make_refl(thy,source,ind);
	}
	Rewriter subst( Intp const& intp ) const;
private:
	size_t _get_ind( Opt<std::string> const& rel ) const;
	Opt<Thm> _step( Rules const& rules, Thy const& thy, CTerm const& source, size_t ind ) const;
	Opt<Thm> _step_abs( Rules const& rules, Thy const& thy, CTerm const& source, size_t ind, CTerm const& assm, Subst const& subst ) const;
	Opt<Thm> _step( Rules const& rules, Thy const& thy, CTerm const& source, size_t ind, std::vector<char>::const_iterator it, std::vector<char>::const_iterator end ) const;
	Opt<Thm> _step_abs( Rules const& rules, Thy const& thy, CTerm const& source, size_t ind, std::vector<char>::const_iterator it, std::vector<char>::const_iterator end ) const;
	Opt<Thm> _steps( Rules const& rules, Thy const& thy, CTerm const& source, size_t min, size_t max, bool safe, std::vector<char> const& pos, size_t ind ) const;
	Thm _make_refl( Thy const& thy, CTerm const& source, size_t ind ) const;
	friend std::ostream& operator<<( std::ostream& os, Rule const& rule );
};

inline std::ostream& operator<<( std::ostream& os, Rewriter::Rule const& rule ) {
	return os << '[' << rule.pat << "] " << rule.rule;
}
#endif
