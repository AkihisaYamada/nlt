#ifndef ELIM_HPP_
#define ELIM_HPP_

#include "util.hpp"

class Elim {
	Thm _thm;//  Γ ⊢ ∀x... φ ⟹ τ ⟹... ψ
	Thm _rule;// Γ. fix x... assume φ, τ... ⊢ ψ
	Thm _premise;// Γ. fix x... assume φ, τ... ⊢ φ
	unsigned short _guards;// number of guards τ... 
	unsigned short _after;// how many premises are remaining
	char _mode;// intro or rewrite
	explicit Elim( Thm const& thm, Thm const& premise, Thm const& rule, short guards, short after, char mode ) :
		_thm(thm), _premise(premise), _rule(rule), _guards(guards), _after(after), _mode(mode) {
	}
public:
	static Elim rule( Thm const& thm, short guards, short after, char mode );
	/** matches a theorem against the premise of elimination.
	 * @param arg the theorem to eliminate
	 * @param thy the theory arg belongs
	 */
	Opt<Subst> matches( Thm const& arg, Opt<Subst const&> subst ) const {
		auto ret = match(_premise,arg,is_patvar,subst);
		if( ret ) {
		}
		return ret;
	}
	ElimRes instantiate( Resolver& sol, Subst& m, Thm const& arg, Intp const& intp, Thy const& thy ) const;
	Ctxt ctxt() && = delete;
	Ctxt const& ctxt() const& {
		return _premise.ctxt();
	}
	Thm thm() const {
		return _thm;
	}
	Thm premise() const {
		return _premise;
	}
	bool operator<( Elim const& y ) const {
		return _premise < y._premise;
	}
};

#endif