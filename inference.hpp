#ifndef _INFERENCE_HPP
#define _INFERENCE_HPP

#include "rewriter.hpp"

/** @brief Add concluder theorem to theory */
void add_forced( Thy&, Thm const& thm, bool allow_intro = false );

/** Class for inference */
class Inference {
	Thy _thy;
	Thm _thm;
	CTerm _claim;
	size_t _goals;
	Inference( Thy const& thy, Thm const& thesis, CTerm const& claim, size_t goals ) :
		_thy(thy), _thm(thesis), _claim(claim), _goals(goals) {}
public:
	struct Ctrl {
		size_t fuel = 255;
		size_t trial = 1;
		bool force_assms = false;
		std::set<Intro> intros;
		std::set<Elim> elims;
		Opt<std::pair<Rewriter::Rules,Rewriter::Ctrl>> rewrite;
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
	static Inference claim_exact( Thy const& thy, CTerm const& claim ) {
		auto intp = claim.ctxt().fork();
		auto thesis = intp.ctxt().assume(claim.subst(intp)).intro();// claim ⟹ claim
		return Inference( thy, thesis, claim, 1 );
	}
	static Inference make( Thy const& thy, Thm const& thesis ) {
		CTerm claim = thesis;
		size_t goals = 0;
		while( auto imp = claim.cbinary(IMP) ) {
			claim = imp->second;
			goals++;
		}
		return Inference(thy,thesis,claim,goals);
	}
	Thy const& thy() const& {
		return _thy;
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
		auto child = _thy.branch();
		return _apply(rule,child.weaken(goal()),child);
	}
	void apply( Intro const& rule ) & {
		if( !applies(rule) ) throw Unapplicable(goal())(rule.conclusion());
	}
	/** @brief Tries to apply a set of rules once */
	void apply( std::set<Intro> const& rules ) & {
		auto child = _thy.branch();
		auto g = strip_all(goal(),*child.parent());
		if( !_apply(rules,g,child) ) throw Unapplicable(g);
	}
	/** @brief Applies set of rules many times */
	void apply( std::set<Intro> const& rules, size_t min, size_t max, bool safe, bool wide ) & {
		size_t suc = 0;
		_apply(rules,suc,min,max,safe,wide);
	}
	/** @brief Discharge goal by identical theorem */
	void discharge( Thm const& thm ) & {
		if( _goals == 0 ) throw NoGoal;
		_thm = _thm.discharge(thm);
		_goals--;
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
	Thm blast_all( Ctrl const& ctrl = DEFAULT_CTRL ) & {
		while( _goals > 0 ) {
			blast(ctrl);
		}
		return _thm;
	}
	/** @brief applies rewriting */
	bool rewrites( Rewriter::Rules const& rules ) &;
	/** @brief applies rewriting with control */
	bool rewrites( Rewriter::Rules const& rules, Ctrl const& ctrl ) &;
	/** @brief pushes the top subgoal into assumption.
	 * @return false if there will be no further subgoal */
	bool push() & {
		if( _goals < 2 ) return false;
		_thy = _thy.branch();
		auto const& weaken = *_thy.parent();
		auto assm = _thy.assume(goal().subst(weaken));
		add_forced(_thy,assm);
		_thm = _thm.subst(weaken).discharge(assm);
		_goals--;
		return true;
	}
	void pop() & {
		auto p = _thy.parent();
		assert(p);
		_thy = p->source();
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
	bool _apply( Intro const& intro, CTerm const& goal, Thy const& child ) &;
	bool _apply( std::set<Intro> const& intros, CTerm const& goal, Thy const& child ) & {
		for( auto const& rule : intros ) {
			if( _apply(rule,goal,child) ) return true;
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
	Thy const& thy,
	Inference::Ctrl const& ctrl
) {
	auto x = Inference::claim_exact(thy,claim);
	if( x.blasts(ctrl) ) {
		return *x.concluding();
	}
	return {};
}
inline Thm prove(
	CTerm const& claim,
	Thy const& thy,
	Inference::Ctrl const& ctrl
) {
	auto x = Inference::claim_exact(thy,claim);
	x.blast(ctrl);
	return *x.concluding();
}
/**
 * @brief Blasts first assumption of implication.
 * 
 * @param thy the theory which tells blast the lemmas to use
 * @return Thm the conclusion
 */
inline Opt<Thm> blasts(
	Thm const& thesis,
	Thy const& thy,
	Inference::Ctrl const& ctrl = Inference::DEFAULT_CTRL
) {
	if( auto imp = thesis.cbinary(IMP) )
	if( auto prem = proves(imp->first,thy,ctrl) ) {
		return thesis.discharge(*prem);
	}
	return {};
}
inline Thm blast(
	Thm const& thesis,
	Thy const& thy,
	Inference::Ctrl const& ctrl = Inference::DEFAULT_CTRL
) {
	auto imp = thesis.cbinary(IMP);
	if( !imp ) throw Error("nothing to blast");
	return thesis.discharge(prove(imp->first,thy,ctrl));
}

std::ostream& operator<<( std::ostream& os, Inference::Ctrl const& ctrl );

#endif