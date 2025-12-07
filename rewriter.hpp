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
	friend Inference;
	friend Thy;
public:
	static std::string const CONG;
	struct Error : ::Error {
		static inline Term const RT = "#rewriter";
		Error(Term const& term) : ::Error(RT(term)) {}
	};
	class Rules : std::vector<std::vector<Rule>> {
		Rules( size_t n ) : std::vector<std::vector<Rule>>(n) {}
		friend Rewriter;
		friend Thy;
		friend Inference;
	};
	struct Ctrl {
		Opt<std::string> rel;
		std::vector<char> pos;
		size_t min, max;
		bool safe;
		size_t fuel = 255;
		size_t trial = 1;
	};
	static Ctrl const DEFAULT_CTRL;
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
	Rewriter& register_imp( Thm const& thm, bool dir ) &;
	Rewriter& register_refl( Thm const& thm, bool def ) &;
	Rewriter& register_trans( Thm const& thm ) &;
	Rewriter& register_cong( Thm const& thm ) &;
	Rewriter& register_dual( Thm const& thm ) &;
	Rewriter& register_to_true( Thm const& thm ) &;
	Rewriter subst( Intp const& intp ) const;
	void add_rule( Rules& rules, Thm const& thm, Thy const& thy ) const&;
private:
	size_t _get_ind( Opt<std::string> const& rel ) const;
	friend std::ostream& operator<<( std::ostream& os, Rule const& rule );
};

inline std::ostream& operator<<( std::ostream& os, Rewriter::Rule const& rule ) {
	return os << '[' << rule.pat << "] " << rule.rule;
}
#endif
