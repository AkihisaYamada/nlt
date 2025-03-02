#ifndef _INFERENCE_HPP
#define _INFERENCE_HPP

#include "locale.hpp"

/** @brief Add concluder theorem to locale */
void add_forced( Locale&, Thm const& thm );

/** Introduction rule */
class Intro {
	friend class Inference;
	Thm _conclusion;
	explicit Intro( Thm const& conc ) : _conclusion(conc) {}
public:
	static Intro just( Thm const& thm ) {
		return Intro(thm.weaken(thm.ctxt().branch()));
	}
	/** @brief Makes implication a rule. */
	static Intro imp( Thm const& thm );
	/** @brief Makes a theorem into a rule. */
	static Intro rule( Thm const& thm );
	/** @brief Makes a theorem into an axiom.
	 * universal quantifications are processed but not implications.
     */
	static Intro axiom( Thm const& thm ) {
		return Intro(strip_all(thm));
	}
	Thm const& conclusion() const& {
		return _conclusion;
	}
	Thm thm() const& {
		return _conclusion.intro();
	}
	Opt<CSubst> matches( CTerm const& goal ) const {
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
	Thm _premise;
	Thm _thm;
	explicit Elim( Thm const& premise, Thm const& thm ) : _premise(premise), _thm(thm) {}
public:
	static Elim rule( Thm const& thm ) {
		Ctxt ctxt = thm.ctxt().branch();
		Thm body = strip_all(thm,ctxt);
		auto imp = body.cbinary(IMP);
		if( !imp ) throw Error("\"malformed elimination rule\"")(thm);
		Thm premise = ctxt.assume(imp->first);
		return Elim(premise,body.discharge(premise));
	}
	Opt<CSubst> matches( Thm const& assm ) const {
		return match( _premise, assm, [&](auto v){ return ctxt().fixes(v); } );
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
	/** @brief instantiates the rule. */
	Thm subst( Intp const& intp ) const {
		return intp.subst(_thm);
	}
	bool operator<( Elim const& y ) const {
		return _premise < y._premise;
	}
};

/** Class for inference */
class Inference {
	Locale _loc;
	Thm _thm;
	CTerm _claim;
	size_t _goals;
	Inference( Locale const& loc, Thm const& thesis, CTerm const& claim, size_t goals ) :
		_loc(loc), _thm(thesis), _claim(claim), _goals(goals) {}
public:
	/** name for introduction rules */
	static std::string const INTRO;
	/** name for schematic concluders */
	static std::string const CONCL;
	/** name for exact concluder */
	static std::string const EXACT;
	/** name for elimination rules */
	static std::string const ELIM;
	static Error const NoGoal;
	static Error const Unapplicable;
	static Inference claim_exact( Locale const& loc, CTerm const& claim ) {
		Ctxt ctxt = claim.ctxt().branch();
		return Inference( loc, ctxt.assume(claim.weaken(ctxt)).intro(), claim, 1 );// claim ⟹ claim
	}
	Locale const& locale() const& {
		return _loc;
	}
	Thm thm() const {
		return _thm;
	}
	bool ready() const {
		return _goals == 0;
	}
	size_t goal_count() const {
		return _goals;
	}
	Opt<CTerm> has_goal() const& {
		if( _goals != 0 ) {
			auto imp = _thm.cbinary(IMP);
			assert(imp);
			return imp->first;
		}
		return {};
	}
	CTerm goal() const& {
		if( _goals == 0 ) throw NoGoal;
		auto imp = _thm.cbinary(IMP);
		assert(imp);
		return imp->first;
	}
	Opt<Thm> concluding() const& {
		if( _goals == 0 ) return _thm;
		return {};
	}
	/** @brief Tries to apply a rule once */
	void apply( Intro const& rule ) & {
		auto g = strip_all(goal());
		if( !_apply(rule,g) ) throw Unapplicable(g)(rule.conclusion());
	}
	/** @brief Tries to apply a set of rules once */
	void apply( std::set<Intro> const& rules ) & {
		auto g = strip_all(goal());
		if( !_apply(rules,g) ) throw Unapplicable(g);
	}
	/** @brief Applies set of rules many times */
	void apply( std::set<Intro> const& rules, size_t min, size_t max, bool safe, bool deep ) & {
		size_t suc = 0;
		_apply(rules,suc,min,max,safe,deep);
	}
	void _apply( std::set<Intro> const& rules, size_t& suc, size_t min, size_t max, bool safe, bool deep ) &;
	/** @brief Discharge goal by identical theorem */
	void discharge( Thm const& thm ) & {
		if( _goals == 0 ) throw NoGoal;
		if( !_discharges(thm) ) throw Error("\"not exact\"")(thm);
	}
	void elim( std::set<Elim> const& elims ) &;
	void blast(
		size_t& fuel,
		std::set<Intro> const& intros = {},
		std::set<Elim> const& elims = {},
		std::function<bool(Inference&)> extra = [](auto){ return false; }
	) &;
	void blast_all(
		size_t& fuel,
		std::set<Intro> const& intros = {},
		std::set<Elim> const& elims = {},
		std::function<bool(Inference&)> extra = [](auto){ return false; }
	) & {
		while( _goals > 0 ) {
			if( fuel == 0 ) throw Error("\"blast exceeded\"")(*has_goal());
			blast(fuel,intros,elims,extra);
		}
	}

	/** @brief pushes the top subgoal into assumption.
	 * @return false if there will be no further subgoal */
	bool push() & {
		if( _goals < 2 ) return false;
		_loc = _loc.branch();
		auto assm = _loc.assume(goal().weaken(_loc));
		add_forced(_loc,assm);
		_thm = _thm.weaken(_loc).discharge(assm);
		_goals--;
		return true;
	}
	void pop() & {
		auto p = _loc.parent();
		assert(p);
		_loc = *p;
		_thm = _thm.intro();
		_goals++;
	}

private:
	bool _discharges( Thm const& thm ) & {
		if( auto o = _thm.discharges(thm) ) {
			_thm = *o;
			_goals--;
			return true;
		}
		return false;
	}
	/** goal must be in a fresh context */
	bool _apply( Intro const& intros, CTerm const& goal ) &;
	bool _apply( std::set<Intro> const& intros, CTerm const& goal ) & {
		for( auto const& rule : intros ) {
			if( _apply(rule,goal) ) return true;
		}
		return false;
	}
};

inline Thm prove(
	CTerm const& claim,
	Locale const& loc,
	std::set<Intro> const& intros = {},
	std::set<Elim> const& elims = {},
	std::function<bool(Inference&)> extra = [](auto){ return false; }
) {
	auto x = Inference::claim_exact(loc,claim);
	size_t fuel = 255;
	x.blast(fuel,intros,elims,extra);
	return *x.concluding();
}
/**
 * @brief Blasts first assumption of implication.
 * 
 * @param loc the locale which tells blast the lemmas to use
 * @return Thm the conclusion
 */
inline Opt<Thm> blasts(
	Thm const& thesis,
	Locale const& loc,
	std::set<Intro> const& intros = {},
	std::set<Elim> const& elims = {},
	std::function<bool(Inference&)> extra = [](auto){ return false; }
) {
	if( auto imp = thesis.cbinary(IMP) ) {
		return thesis.discharge(prove(imp->first,loc,intros,elims,extra));
	}
	return {};
}
inline Thm blast(
	Thm const& thesis,
	Locale const& loc,
	std::set<Intro> const& intros = {},
	std::set<Elim> const& elims = {},
	std::function<bool(Inference&)> extra = [](auto){ return false; }
) {
	auto opt = blasts(thesis,loc,intros,elims,extra);
	assert(opt);
	return *opt;
}



#endif