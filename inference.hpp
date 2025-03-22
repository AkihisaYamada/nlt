#ifndef _INFERENCE_HPP
#define _INFERENCE_HPP

#include "locale.hpp"

/** @brief Add concluder theorem to locale */
void add_forced( Locale&, Thm const& thm, bool allow_intro = false );

/** Class for inference */
class Inference {
	Locale _loc;
	Thm _thm;
	CTerm _claim;
	size_t _goals;
	Inference( Locale const& loc, Thm const& thesis, CTerm const& claim, size_t goals ) :
		_loc(loc), _thm(thesis), _claim(claim), _goals(goals) {}
public:
	struct Ctrl {
		size_t fuel = 255;
		size_t trial = 1;
		bool force_assms = false;
		std::set<Intro> intros;
		std::set<Elim> elims;
		std::function<bool(Inference&)> extra = [](auto){ return false; };
	};
	static const Ctrl DEFAULT_CTRL;
	/** name for exact concluder */
	static std::string const EXACT;
	/** name for introduction rules */
	static std::string const INTRO;
	/** name for weak introduction rules */
	static std::string const WEAK;
	/** name for schematic concluders */
	static std::string const CONCL;
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
	bool applies( Intro const& rule ) & {
		return _apply(rule,goal().weaken(goal().ctxt().branch()));
	}
	void apply( Intro const& rule ) & {
		auto g = goal().weaken(goal().ctxt().branch());
		if( !_apply(rule,g) ) throw Unapplicable(g)(rule.conclusion());
	}
	/** @brief Tries to apply a set of rules once */
	void apply( std::set<Intro> const& rules ) & {
		auto g = strip_all(goal());
		if( !_apply(rules,g) ) throw Unapplicable(g);
	}
	/** @brief Applies set of rules many times */
	void apply( std::set<Intro> const& rules, size_t min, size_t max, bool safe, bool wide ) & {
		size_t suc = 0;
		_apply(rules,suc,min,max,safe,wide);
	}
	/** @brief Discharge goal by identical theorem */
	void discharge( Thm const& thm ) & {
		if( _goals == 0 ) throw NoGoal;
		if( !_discharges(thm) ) throw Error("\"not exact\"")(goal())(thm);
	}
	void elim( std::set<Elim> const& elims ) &;
	bool blasts( Ctrl const& ctrl = DEFAULT_CTRL ) & {
		std::vector<Intro> elim_res;
		size_t fuel = ctrl.fuel;
		return _blast(fuel,1,ctrl,true,elim_res,0);
	}
	void blast( Ctrl const& ctrl = DEFAULT_CTRL ) & {
		std::vector<Intro> elim_res;
		size_t fuel = ctrl.fuel;
		_blast(fuel,1,ctrl,false,elim_res,0);
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
	bool _apply( Intro const& intro, CTerm const& goal ) &;
	bool _apply( std::set<Intro> const& intros, CTerm const& goal ) & {
		for( auto const& rule : intros ) {
			if( _apply(rule,goal) ) return true;
		}
		return false;
	}
	void _apply( std::set<Intro> const& rules, size_t& suc, size_t min, size_t max, bool safe, bool wide ) &;
	bool _apply_blast(
		size_t& fuel,
		size_t trial,
		CTerm const& goal,
		Intro const& intro,
		Ctrl const& ctrl
	) &;
	bool _blast(
		size_t& fuel,
		size_t trial,
		Ctrl const& ctrl,
		bool fail,
		std::vector<Intro>& elim_res,
		size_t elim_res_ind
	) &;
};

inline const Inference::Ctrl Inference::DEFAULT_CTRL;

inline Opt<Thm> proves(
	CTerm const& claim,
	Locale const& loc,
	Inference::Ctrl const& ctrl = Inference::DEFAULT_CTRL
) {
	auto x = Inference::claim_exact(loc,claim);
	if( x.blasts(ctrl) ) {
		return *x.concluding();
	}
	return {};
}
inline Thm prove(
	CTerm const& claim,
	Locale const& loc,
	Inference::Ctrl const& ctrl = Inference::DEFAULT_CTRL
) {
	auto x = Inference::claim_exact(loc,claim);
	x.blast(ctrl);
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
	Inference::Ctrl const& ctrl = Inference::DEFAULT_CTRL
) {
	if( auto imp = thesis.cbinary(IMP) )
	if( auto prem = proves(imp->first,loc,ctrl) ) {
		return thesis.discharge(*prem);
	}
	return {};
}
inline Thm blast(
	Thm const& thesis,
	Locale const& loc,
	Inference::Ctrl const& ctrl = Inference::DEFAULT_CTRL
) {
	auto imp = thesis.cbinary(IMP);
	if( !imp ) throw Error("nothing to blast");
	return thesis.discharge(prove(imp->first,loc,ctrl));
}



#endif