#ifndef _UTIL_HPP_
#define _UTIL_HPP_

#include<ostream>
#include"syntax.hpp"

inline std::string operator+( std::string x, std::string_view const& y ) {
	x+=y;
	return x;
}

extern Term const DUMMY;

/** comparison of terms */
int compare_term( Term const& l, Term const& r );
/** comparison of terms */
bool operator<( Term const& l, Term const& r );

/** makes the theorem t ⟹ t */
inline Thm make_refl( CTerm const& t ) {
	auto intp = t.ctxt().branch();
	return intp.ctxt().assume(t.subst(intp)).intro();
}

/** Iterate over locally fixed variables. */
inline void iter_local_vars( Ctxt const& ctxt, std::function<void(std::string const&)> f ) {
	for( size_t i = 0; i < ctxt.revision(); i++ ) {
		if( auto const& fix = ctxt.fixed(i) ) {
			f(*fix);
		}
	}
}

using Renamer = std::function<Opt<std::string>(std::string_view const&)>;

/**
 * @brief default renamer.
 * 
 * @param ctxt 
 * @return function that always gives a fresh name in the context.
 */
Renamer avoider(Ctxt const& ctxt);

/** Fresh variable maker */
Renamer fresh_maker();

/**
 * @brief strips universal quantifiers.
 * @param t ∀x... φ
 * @param intp interpretation of the context of `t` in the context that will fix the bound variables
 * @param renamer
 * @return closed term φ in context
 */
CTerm strip_all( CTerm t, Intp const& intp, Renamer const& renamer );

/**
 * @brief strips universal quantifiers with default renaming
 */
inline CTerm strip_all( CTerm const& t, Intp const& intp ) {
	return strip_all(t,intp,avoider(intp.ctxt()));
}

/**
 * @brief strips universal quantifiers.
 * @param thm the theorem to be stripped.
 * @param child this context will fix the bound variables.
 */
std::pair<Thm,size_t> strip_all( Thm const& thm, Intp const& child, Renamer const& renamer );

inline std::pair<Thm,size_t> strip_all( Thm const& thm, Intp const& child ) {
	return strip_all(thm,child,avoider(child.ctxt()));
}
/**
 * @brief strips universal quantifiers.
 * @param thm the theorem to be stripped.
 * @return Intp this context will fix the bound variables.
 */
inline std::tuple<Thm,Intp,size_t> strip_all( Thm const& thm ) {
	auto child = thm.ctxt().branch();
	auto [strip_thm,n] = strip_all(thm,child);
	return {strip_thm,child,n};
}

/**
 * @brief instantiate by substitution
 * 
 * @param intp 
 * @param subst 
 */
void subst_intp( Intp& intp, Subst& subst );

/** @brief 
 * @param imp ∀x... φ ⟹ ψ
 * @param arg φθ
 * @return ∀y... ψθ
 */
Thm match_discharge( Thm const& imp, Thm const& arg );

/**
 * @brief Uncurrying
 * 
 * @param t 
 * @return std::pair<std::string,std::vector<Term>> 
 */
std::pair<std::string,std::list<Term>> uncurry(Term const& t);

/**
 * @brief Strip binary operator
 * 
 * @param t 
 * @return std::tuple<std::string,CTerm,CTerm> 
 */
Opt<std::tuple<std::string,CTerm,CTerm>> strips_binary(CTerm const& t);

/**
 * @brief Matching, assuming disjoint free variables.
 * @param pat 
 * @param val 
 * @param fvar signifies free variables.
 */
Opt<Subst> match( CTerm const& pat, CTerm const& val, std::function<bool(std::string_view const&)> const& fvar );

/**
 * @brief Unification.
 * The input two terms must be closed with respect to a context.
 * @param l 
 * @param r 
 * @param fvar signifies free variables.
 * @return an idempotent, most general unifier iff `l` and `r` are unifiable.
 */
Opt<Subst> unify(CTerm const& l, CTerm const& r, std::function<bool(std::string const&)> const& fvar);

/**
 * @brief Automatically instantiate universally quantified variables so that implication premises are discharged.
 * 
 * @param t should be of form ∀x... (∀y... φ) ⟹ ψ
 * @param arg should be of form ∀z... χ, where φ and χ are unifiable by θ
 * @return the resulting theorem, ∀w... ψθ
 */
Thm discharge(Thm t, Thm arg);

/** Discharge */
inline Thm operator<<(Thm const& t, Thm arg) {
	return discharge(t,arg);
}

/** detects trivial abstraction x. y.[x], and returns y */
Opt<std::string> virtual_var( CTerm const& t );

/** Introduction rule */
class Intro {
	friend class Elim;
	Thm _thm;// Γ ⊢ ∀x... φ... ⟹ ψ
	Thm _conclusion;// Γ. fix x... assume φ... ⊢ ψ
	size_t _vars, _conds;
	explicit Intro( Thm const& thm, Thm const& conc, size_t vars, size_t conds ) :
		_thm(thm), _conclusion(conc), _vars(vars), _conds(conds) {
	}
public:
	size_t vars() const {
		return _vars;
	}
	size_t conds() const {
		return _conds;
	}
	static Intro just( Thm const& thm ) {
		auto child = thm.ctxt().branch();
		return Intro(thm,thm.subst(child),0,0);
	}
	/** @brief Makes implication a rule. */
	static Intro imp( Thm const& thm, size_t n = 1 );
	/** @brief Makes a theorem into a rule. */
	static Intro rule( Thm const& thm );
	/** @brief Makes a theorem into an axiom.
	 * universal quantifications are processed but not implications.
     */
	static Intro axiom( Thm const& thm ) {
		auto [conc,intp,vars] = strip_all(thm);
		return Intro(thm,conc,vars,0);
	}
	Thm const& conclusion() const& {
		return _conclusion;
	}
	Thm const& thm() const& {
		return _thm;
	}
	Opt<Subst> matches( CTerm const& goal ) const {
		return match( _conclusion, goal, [&](auto v){ return _conclusion.ctxt().fixes(v); } );
	}
	/** @brief instantiates the rule. */
	Thm subst( Intp const& intp ) const {
		return _conclusion.subst(intp);
	}
	bool operator<( Intro const& y ) const {
		return _conclusion < y._conclusion;
	}
};

class Elim {
	Thm _thm;// ∀thesis. ψ... ⟹ thesis, where the context fixes other variables and assumes premise φ
	Thm _premise;// φ
	explicit Elim( Thm const& premise, Thm const& thm ) : _premise(premise), _thm(thm) {}
public:
	static Elim rule( Thm const& thm );
	Opt<Intro> matches( Thm const& assm, Intp const& intp ) const {
		auto pat_ctxt = _premise.ctxt();
		auto m = match( _premise, assm, [&](auto v){ return pat_ctxt.fixes(v); } );
		if( !m ) return {};
		auto pat_intp = Intp::make(pat_ctxt,intp.source()).compose(intp);
		subst_intp(pat_intp,*m);
		pat_intp.discharge(assm);
		auto thm = _thm.subst(pat_intp);// ∀thesis. ψθ... ⟹ thesis
		return Intro::rule(thm);
	}
	Ctxt ctxt() && = delete;
	Ctxt const& ctxt() const& {
		return _premise.ctxt();
	}
	Thm premise() const {
		return _premise;
	}
	bool operator<( Elim const& y ) const {
		return _premise < y._premise;
	}
};

class Inference;

#endif