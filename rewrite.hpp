#ifndef _REWRITE_HPP_
#define _REWRITE_HPP_

#include"util.hpp"

class Thy;

class Resolver;
/**
 * @brief Rewrite information
 * 
 */
class Rewrite {
public:
	class Rule {
		friend Rewrite;
		friend Resolver;
		friend Thy;
		struct Cond {
			Opt<size_t> ind;
			bool abs;
			bool rec;// allow recursive rewriting
			CTerm assm;// φ or x. φ if abs
		};
		Thm thm;// Γ ⊢ ∀x...y... φ... ⟹ l[x...] = r[y...]
		Thm concl;// Γ.fix x...y... assume φ... ⊢ l[x...] = r[y...]
		CTerm pat;// Γ.fix x...y... assume φ... ⊢ l[x...]
		std::vector<Cond> conds;
		bool cong;// at least one condition must be rewritten
		Rule( Thm const& concl, CTerm const& pat, Thm const& thm, std::vector<Cond> && conds, bool cong ) : concl(concl), pat(pat), thm(thm), conds(std::move(conds)), cong(cong) {}
	public:
		operator Thm() const& {
			return thm;
		}
	};
private:
	struct Imp {
		Thm thm;// s = t ⟹ conditions ... ⟹ s ⟹ t
		size_t conds;// number of conditions
	};
	/** relation symbols, e.g., ⟺ or = */
	std::vector<std::string> _rels;
	StrMap<size_t const> _rel2ind;
	/** reflexivity theorems, e.g., ∀x. x = x */
	std::vector<Thm> _refls;
	/** ∀x y z. x = y ⟹ y = z ⟹ x = z */
	Map<size_t,Thm> _trans;
	/** ∀P Q. P = Q ⟹ P ⟹ Q */
	Map<size_t,Imp> _imps;
	/** ∀P Q. P = Q ⟹ Q ⟹ P */
	Map<size_t,Imp> _revimps;
	/** ∀x y x' y'. x = x' ⟹ y = y' ⟹ x + y = x' + y' */
	std::vector<std::vector<Rule>> _congs;
	/** ∀P Q. P = Q ⟹ P ⟺ Q */
	Map<size_t,Rule> _fallbacks;
	/** ∀P. P ⟹ P = true */
	Opt<std::pair<Thm,size_t>> _to_true;
	size_t _default_ind;
	friend Resolver;
	friend Thy;
public:
	struct Error : ::Error {
		static inline Term const RT = "#rewriter";
		Error(Term const& term) : ::Error(RT(term)) {}
	};
	class Rules : std::vector<std::vector<Rule>> {
		Rules( size_t n ) : std::vector<std::vector<Rule>>(n) {}
		friend Rewrite;
		friend Thy;
		friend Resolver;
	};
	bool empty() const {
		return _rels.empty();
	}
	std::vector<std::string> const& rels() const {
		return _rels;
	}
	Rules make_rules() const {
		return Rules(_rels.size());
	}
	Opt<size_t> gets_rel_ind( std::string_view const& rel ) const {
		return _rel2ind.finds_value(rel);
	}
	Thm get_refl( size_t ind ) const {
		assert( ind < _refls.size() );
		return _refls[ind];
	}
	bool register_refl( Thm const& thm, bool def ) &;
	void register_imp( Thm const& thm, bool dir ) &;
	void register_trans( Thm const& thm ) &;
	/** Congruence rules should be in form `∀x... y... x = y... ⟹ φ... ⟹ l[x...] = r[y...]` */
	std::tuple<char,std::string,Rule> make_rule( Thm const& thm, bool cong ) const&;
	bool register_cong( Thm const& thm ) &;
	void register_fallback( Thm const& thm ) &;
	void register_to_true( Thm const& thm ) &;
	void add_rewrite_rule( Rewrite::Rules& rules, Thm const& thm, bool cong ) const &;
	void import( Rewrite const& src, Thy const& thy, Intp const& intp, bool override_default ) &;
	size_t get_ind( Opt<std::string> const& rel ) const &;
};

#endif
