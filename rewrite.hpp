#ifndef _REWRITE_HPP_
#define _REWRITE_HPP_

#include"util.hpp"

class Thy;

class Blaster;
/**
 * @brief Rewrite information
 * 
 */
class Rewrite {
public:
	class Rule {
		CTerm _pat;// Γ.fix x... assume φ... ⊢ l
		Thm _rule;//  Γ.fix x... assume φ... ⊢ l = r
		Ctxt _ctxt;// Γ, holding ∀x... φ ⟹... l = r
		friend Rewrite;
	public:
		Rule( CTerm const& pat, Thm const& rule, Ctxt const& ctxt ) : _pat(pat), _rule(rule), _ctxt(ctxt) {}
		CTerm const& pat() const& {
			return _pat;
		}
		Thm const& thm() const& {
			return _rule;
		}
		Ctxt const& ctxt() const& {
			return _ctxt;
		}
	};
	struct Cong : Thm {
		struct Cond {
			Opt<size_t> ind;
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
	friend Blaster;
	friend Thy;
public:
	static std::string const CONG;
	struct Error : ::Error {
		static inline Term const RT = "#rewriter";
		Error(Term const& term) : ::Error(RT(term)) {}
	};
	class Rules : std::vector<std::vector<Rule>> {
		Rules( size_t n ) : std::vector<std::vector<Rule>>(n) {}
		friend Rewrite;
		friend Thy;
		friend Blaster;
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
	Rewrite& register_imp( Thm const& thm, bool dir ) &;
	Rewrite& register_refl( Thm const& thm, bool def ) &;
	Rewrite& register_trans( Thm const& thm ) &;
	/** Congruence rules should be in form `∀x... y... x = y... ⟹ φ... ⟹ l[x...] = r[y...]` */
	Rewrite& register_cong( Thm const& thm ) &;
	Rewrite& register_dual( Thm const& thm ) &;
	Rewrite& register_to_true( Thm const& thm ) &;
	Rewrite subst( Intp const& intp ) const;
private:
	size_t _get_ind( Opt<std::string> const& rel ) const;
	friend std::ostream& operator<<( std::ostream& os, Rule const& rule );
};

inline std::ostream& operator<<( std::ostream& os, Rewrite::Rule const& rule ) {
	return os << '[' << rule.pat() << "] " << rule.thm();
}
#endif
