#ifndef _INFERENCE_HPP
#define _INFERENCE_HPP

#include "theory.hpp"

class Resolver;

/** @brief Add concluder theorem to theory */
void add_intro( Thy& thy, Thm const& thm, Intro const& rule, bool allow_intro = false );
inline void add_intro( Thy& thy, Thm const& thm, bool allow_intro = false ) {
	add_intro(thy,thm,Intro::rule(thm),allow_intro);
}

/** Class for inference */
class Thesis {
	Thy _thy;
	Thm _thm;
	CTerm _claim;
	size_t _goals;
	Thesis( Thy const& thy, Thm const& thesis, CTerm const& claim, size_t goals ) :
		_thy(thy), _thm(thesis), _claim(claim), _goals(goals) {}
	friend Resolver;
public:
	static Thesis claim_exact( Thy const& thy, CTerm const& claim ) {
		auto intp = claim.ctxt().fork();
		auto thesis = intp.ctxt().assume(claim.subst(intp)).intro();// claim ⟹ claim
		return Thesis( thy, thesis, claim, 1 );
	}
	static Thesis make( Thy const& thy, Thm const& thesis ) {
		CTerm claim = thesis;
		size_t goals = 0;
		while( auto imp = claim.cbinary(IMP) ) {
			claim = imp->second;
			goals++;
		}
		return Thesis(thy,thesis,claim,goals);
	}
	Thy& thy() & {
		return _thy;
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
		if( _goals == 0 ) throw Error("\"no goal\"");
		auto imp = _thm.cbinary(IMP);
		assert(imp);
		return imp->first;
	}
	Opt<Thm> concluding() const& {
		if( _goals == 0 ) return _thm;
		return {};
	}
	/** @brief Discharge a subgoal by identical theorem */
	void discharge( Thm const& thm ) & {
		if( _goals == 0 ) throw Error("\"no goal\"");;
		_thm = _thm.impE(thm);
		_goals--;
	}
	/** @brief Tries to apply a rule once */
	bool applies( Intro const& rule ) & {
		auto child = _thy.branch();
		return _apply(rule,child.weaken(goal()),child);
	}
	void apply( Intro const& rule ) & {
		if( !applies(rule) ) throw Error("\"not applicable\"")(goal())(rule.conclusion());
	}
	/** @brief Tries to apply a set of rules once */
	void apply( std::set<Intro> const& rules ) & {
		auto child = _thy.branch();
		auto g = strip_all(goal(),*child.parent());
		if( !_apply(rules,g,child) ) throw Error("\"not applicable\"")(g);
	}
	/** @brief Applies set of rules many times */
	void apply( std::set<Intro> const& rules, size_t min, size_t max, bool normalize, bool wide ) & {
		size_t suc = 0;
		_apply(rules,suc,min,max,normalize,wide);
	}
	/** Automatically discharge a subgoal */
	void auto_discharge() &;
	/** Automatically discharge all subgoals */
	Thm discharge_all() &;
	/** skip the first subgoal */
	bool push() & {
		if( _goals < 2 ) return false;
		_thy = _thy.branch();
		auto const& weaken = *_thy.parent();
		auto assm = _thy.assume(goal().subst(weaken));
		add_intro(_thy,assm);
		_thm = _thm.subst(weaken).impE(assm);
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
	/** goal must be in a fresh context */
	bool _apply( Intro const& intro, CTerm const& goal, Thy const& child ) &;
	
	bool _apply( std::set<Intro> const& intros, CTerm const& goal, Thy const& child ) & {
		for( auto const& rule : intros ) {
			if( _apply(rule,goal,child) ) return true;
		}
		return false;
	}
	void _apply( std::set<Intro> const& rules, size_t& suc, size_t min, size_t max, bool safe, bool wide ) &;
	void _apply2( Subst const& matcher, Intro const& intro, Thy const& child, Intp const& rule2child ) &;
};

class Resolver {
	size_t fuel;
	char log;
	unsigned short int indent;
	Opt<Rewrite const&> rew;
	std::vector<std::pair<std::string,AThm>> elim_res;
	friend Rewrite;
	std::ostream& _log() const& {
		int n = indent < 16 ? indent : 16;
		for( int i = 0; i < n; i++ ) {
			std::cerr << ' ';
		}
		return std::cerr;
	}
public:
	Rewrite::Rules rules;
	Resolver( Opt<Rewrite const&> const& rew, char log = 0, size_t fuel = 255 ) : rew(rew), rules( rew ? rew->_refls.size() : 0 ), log(log), indent(1), fuel(fuel) {}
	bool discharges( Thesis& thesis, bool rewrite ) & {
		return _discharge(thesis,1,true,rewrite,elim_res.size());
	}
	void discharge( Thesis& thesis, bool rewrite ) & {
		_discharge(thesis,1,false,rewrite,elim_res.size());
	}
	Thm discharge_all( Thesis& thesis ) & {
		while( thesis._goals > 0 ) {
			discharge(thesis,true);
		}
		return thesis._thm;
	}
	Opt<Thm> proves( Thy const& thy, CTerm const& claim, bool rewrite ) & {
		auto x = Thesis::claim_exact(thy,claim);
		if( discharges(x,rewrite) ) {
			return *x.concluding();
		}
		return {};
	}
	Thm prove( Thy const& thy, CTerm const& claim, bool rewrite ) & {
		auto x = Thesis::claim_exact(thy,claim);
		discharge(x,rewrite);
		return *x.concluding();
	}
	/**
	* @brief Discharges first assumption of implication.
	* 
	* @return Thm the conclusion
	*/
	Opt<Thm> discharges( Thy const& thy, Thm const& thesis, bool rewrite ) & {
		if( auto imp = thesis.cbinary(IMP) )
		if( auto prem = proves(thy,imp->first,rewrite) ) {
			return thesis.impE(*prem);
		}
		return {};
	}
	Thm discharge( Thy const& thy, Thm const& thesis, bool rewrite ) & {
		auto imp = thesis.cbinary(IMP);
		if( !imp ) throw Error("nothing to resolve")(thesis);
		return thesis.impE(prove(thy,imp->first,rewrite));
	}
	/** declare derivable conclusions */
	void inflate( Thy& thy, Thm const& assm ) &;
	/** @brief applies rewriting */
	bool rewrites( Thesis& thesis, bool simp, size_t min, size_t max, bool normalize, std::vector<char> const& pos, Opt<std::string> const& rel ) &;
	/** @brief Rewrites a theorem */
	Thm rewrites( Thy const& thy, Thm const& source, bool simp, size_t min, size_t max, bool normalize, std::vector<char> const& pos ) &;
	/**
	 * @brief returns a rewrite equation for the given source term at given position.
	 * 
	 * @param source the term to be rewritten
	 * @return the equation
	 */
	Thm steps( Thy const& thy, CTerm const& source, bool simp, size_t min, size_t max, bool normalize, std::vector<char> const& pos, Opt<std::string> const& rel ) & {
		size_t ind = rew->get_ind(rel);
		if( auto ret = _steps(thy,source,simp,min,max,normalize,pos,ind) ) {
			return *ret;
		}
		return _make_refl(thy,source,ind);
	}
private:
	bool _apply_and_discharge(
		Thesis& thesis,
		Subst const& matcher,
		Intp const& rule2child,
		size_t trial,
		Intro const& intro
	) &;
	Opt<Thm> _apply_rewrite_rule(
		Thy const& thy,
		Rewrite::Rule const& rule,
		Subst const& matcher,
		Intp const& rule2thy,
		bool simp,
		std::vector<char>::const_iterator pos_it,
		std::vector<char>::const_iterator pos_end
	) &;
	bool _discharge(
		Thesis& thesis,
		size_t trial,
		bool fail,
		bool rewrite,
		size_t elim_res_ind
	) &;
	Thm _make_refl( Thy const& thy, CTerm const& source, char ind ) &;
	Opt<std::pair<Thm,CTerm>> _step( Thy const& thy, CTerm const& source, bool simp, char ind, std::vector<char>::const_iterator it, std::vector<char>::const_iterator end ) &;
	/** rewrites abstraction.
	 * @returns equation, the rhs, and whether rewrite succeeded
	 */
	bool _step_cond( Thy const& thy, Intp& intp, CTerm const& cond, bool rewrite, bool simp, char ind, std::vector<char>::const_iterator it, std::vector<char>::const_iterator end ) &;
	Opt<Thm> _steps( Thy const& thy, CTerm const& source, bool simp, size_t min, size_t max, bool normalize, std::vector<char> const& pos, char ind ) &;
};

inline void Thesis::auto_discharge() & {
	auto inf = Resolver(_thy.rewriter());
	inf.discharge(*this,true);
}
inline Thm Thesis::discharge_all() & {
	while( _goals > 0 ) auto_discharge();
	return _thm;
}
inline Resolver Thy::resolver( char log ) const& {
	return Resolver(rewriter(),log);
}
inline Thm Thy::prove( CTerm const& claim, char log ) const& {
	auto b = resolver(log);
	auto thesis = Thesis::claim_exact(*this,claim);
	return b.discharge_all(thesis);
}

inline std::ostream& operator<<( std::ostream& os, Thesis const& thesis ) {
	return os << thesis.thy().pretty(thesis.thm());
}
#endif