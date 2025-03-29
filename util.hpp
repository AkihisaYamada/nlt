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
	Ctxt ctxt = t.ctxt().branch();
	return ctxt.assume(t.weaken(ctxt)).intro();
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
Renamer avoider(Ctxt& ctxt);

/** Fresh variable maker */
Renamer fresh_maker();

/**
 * @brief strips universal quantifiers.
 * @param t 
 * @param ctxt this context will fix the bound variables.
 * @param renamer
 */
CTerm strip_all( CTerm t, Ctxt& ctxt, Renamer const& renamer );

/**
 * @brief strips universal quantifiers with default renaming
 */
inline CTerm strip_all(CTerm t, Ctxt& ctxt) {
	return strip_all(t,ctxt,avoider(ctxt));
}
inline CTerm strip_all( CTerm thm ) {
	Ctxt ctxt = thm.ctxt().branch();
	return strip_all(thm,ctxt);
}

/**
 * @brief strips universal quantifiers.
 * @param thm the theorem to be stripped.
 * @param loc this context will fix the bound variables.
 */
std::pair<Thm,size_t> strip_all( Thm const& thm, Ctxt& ctxt, Renamer const& renamer );
inline std::pair<Thm,size_t> strip_all( Thm const& thm, Ctxt& ctxt ) {
	return strip_all(thm,ctxt,avoider(ctxt));
}
inline std::pair<Thm,size_t> strip_all( Thm const& thm ) {
	Ctxt ctxt = thm.ctxt().branch();
	return strip_all(thm,ctxt);
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
 * @param t 
 * @param arg
 * @return the resulting theorem.
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
	Thm _conclusion;
	size_t _vars, _conds;
	explicit Intro( Thm const& conc, size_t vars, size_t conds ) :
		_conclusion(conc), _vars(vars), _conds(conds) {}
public:
	size_t vars() const {
		return _vars;
	}
	size_t conds() const {
		return _conds;
	}
	static Intro just( Thm const& thm ) {
		return Intro(thm.weaken(thm.ctxt().branch()),0,0);
	}
	/** @brief Makes implication a rule. */
	static Intro imp( Thm const& thm, size_t n = 1 );
	/** @brief Makes a theorem into a rule. Number of conditions are returned. */
	static Intro rule( Thm const& thm );
	/** @brief Makes a theorem into an axiom.
	 * universal quantifications are processed but not implications.
     */
	static Intro axiom( Thm const& thm ) {
		auto [conc,vars] = strip_all(thm);
		return Intro(conc,vars,0);
	}
	Thm const& conclusion() const& {
		return _conclusion;
	}
	Thm thm() const& {
		return _conclusion.intro();
	}
	Opt<Subst> matches( CTerm const& goal ) const {
		return match( _conclusion, goal, [&](auto v){ return ctxt().fixes(v); } );
	}
	Ctxt ctxt() && = delete;
	Ctxt const& ctxt() const& {
		return _conclusion.ctxt();
	}
	/** @brief interpretation of the rule into given context.
	 * 
	 */
	Intp intp( Ctxt const& tgt ) const {
		return Intp(ctxt(),tgt);
	}
	/** @brief instantiates the rule. */
	Thm inst( Intp const& intp ) const {
		return intp.subst(_conclusion);
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
	Opt<Intro> matches( Thm const& assm ) const {
		auto pat_ctxt = _premise.ctxt();
		auto m = match( _premise, assm, [&](auto v){ return pat_ctxt.fixes(v); } );
		if( !m ) return {};
		auto intp = Intp( pat_ctxt, assm.ctxt() );
		subst_intp(intp,*m);
		intp.discharge(assm);
		auto thm = intp.subst(_thm);// ∀thesis. ψθ... ⟹ thesis
		return Intro::rule(thm);
	}
	Ctxt ctxt() && = delete;
	Ctxt const& ctxt() const& {
		return _premise.ctxt();
	}
	Thm premise() const {
		return _premise;
	}
	/** @brief interpretation of the rule into given context.
	 * 
	 */
	Intp intp( Ctxt const& tgt ) const {
		return Intp(ctxt(),tgt);
	}
	bool operator<( Elim const& y ) const {
		return _premise < y._premise;
	}
};

#endif