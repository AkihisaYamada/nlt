#ifndef _INFERENCE_HPP
#define _INFERENCE_HPP

#include "theory.hpp"

/** name for exact concluder */
extern std::string const EXACT;
/** name for introduction rules */
extern std::string const INTRO;
/** name for weak introduction rules */
extern std::string const WEAK;
/** name for schematic concluders */
extern std::string const CONCL;
/** name for elimination rules */
extern std::string const ELIM;
/** name for inflator rules */
extern std::string const INFLATOR;
/** property for implication rule: ∀P Q. P = Q ⟹ P ⟹ Q */
extern std::string const REWRITE_IMP;
/** property for reverse implication: ∀P Q. P = Q ⟹ Q ⟹ P */
extern std::string const REWRITE_REV;
/** property for reflexivity rule: ∀x. x = x */
extern std::string const REFL;
/** property for dualizer rule, e.g. ∀x y. x = y ⟹ y = x */
extern std::string const DUAL;
/** property for transitivity rules, e.g. ∀x y. x = y ⟹ ∀z. y = z ⟹ x = z */
extern std::string const TRANS;
/** rewriter name for simplifier */
extern std::string const SIMP;
/** prefix for congruence rules */
extern std::string const CONG;

struct ElimRes {
	Thm thm;
	unsigned short guards;
	unsigned short after;
	char mode;
	ElimRes( Thm const& thm, unsigned short guards, unsigned short after, char mode )
	: thm{thm}, guards{guards}, after{after}, mode{mode} {}
};

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
	void apply( Intro const& rule, bool wide ) &;
	/** @brief Tries to apply a set of rules once */
	void apply( std::set<Intro> const& rules ) & {
		auto child = _thy.branch();
		if( !_apply(rules,child.weaken(goal()),child) ) throw Error("\"not applicable\"")(goal());
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
	bool push() &;
	void pop() &;
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
	std::vector<ElimRes> elim_res;
	friend Rewrite;
	std::ostream& _log() const& {
		int n = indent < 16 ? indent : 16;
		for( int i = 0; i < n; i++ ) {
			std::cerr << ' ';
		}
		return std::cerr;
	}
public:
	Opt<Rewrite const&> const rew;
	Rewrite::Rules rules;
	Resolver( Opt<Rewrite const&> const& rew = {}, char log = 0, size_t fuel = 4096 ) : rew(rew), rules( rew ? rew->_rels.size() : 0 ), log(log), indent(1), fuel(fuel) {}
	bool discharges( Thesis& thesis, Opt<std::string const&> simp ) & {
		return _discharge(thesis,1,true,simp,elim_res.size());
	}
	void discharge( Thesis& thesis, Opt<std::string const&> simp ) & {
		_discharge(thesis,1,false,simp,elim_res.size());
	}
	Thm discharge_all( Thesis& thesis ) & {
		while( thesis._goals > 0 ) {
			discharge(thesis,{SIMP});
		}
		return thesis._thm;
	}
	Opt<Thm> proves( Thy const& thy, CTerm const& claim, Opt<std::string const&> simp ) & {
		auto x = Thesis::claim_exact(thy,claim);
		if( discharges(x,simp) ) {
			return *x.concluding();
		}
		return {};
	}
	Thm prove( Thy const& thy, CTerm const& claim, Opt<std::string const&> simp ) & {
		auto x = Thesis::claim_exact(thy,claim);
		discharge(x,simp);
		return *x.concluding();
	}
	/**
	* @brief Discharges first assumption of implication.
	* 
	* @return Thm the conclusion
	*/
	Opt<Thm> discharges( Thy const& thy, Thm const& thesis, Opt<std::string const&> simp ) & {
		if( auto imp = thesis.cbinary(IMP) )
		if( auto prem = proves(thy,imp->first,simp) ) {
			return thesis.impE(*prem);
		}
		return {};
	}
	Thm discharge( Thy const& thy, Thm const& thesis, Opt<std::string const&> simp ) & {
		auto imp = thesis.cbinary(IMP);
		if( !imp ) throw Error("nothing to resolve")(thesis);
		return thesis.impE(prove(thy,imp->first,simp));
	}
	void discharge( Thy const& thy, Intp& intp ) {
		auto assm = intp.assuming();
		if( !assm ) throw Error("no assumption to resolve");
		intp.discharge(prove(thy,*assm,{}));
	}
	/** @brief applies rewriting */
	bool rewrites( Thesis& thesis, Opt<std::string const&> simp, size_t min, size_t max, bool normalize, bool wide, std::vector<char> const& pos, Opt<std::string const&> rel ) &;
	/** @brief Rewrites a theorem */
	Thm rewrites( Thy& thy, Thm const& source, Opt<std::string const&> simp, size_t min, size_t max, bool normalize, std::vector<char> const& pos, Opt<std::string const&> rel ) &;
	/**
	 * @brief returns a rewrite equation for the given source term at given position.
	 * 
	 * @param source the term to be rewritten
	 * @return the equation
	 */
	Thm steps( Thy& thy, CTerm const& source, Opt<std::string const&> simp, size_t min, size_t max, bool normalize, std::vector<char> const& pos, std::string const& rel ) & {
		if( auto ret = _steps(thy,source,simp,min,max,normalize,pos,rel) ) {
			return *ret;
		}
		return _make_refl(thy,source,rel);
	}
	/** declare derivable conclusions */
	void inflate( Thy& thy, Thm const& assm );
	/** @brief Add concluder theorem to theory */
	void add_intro( Thy& thy, Intro const& rule, bool allow_intro = false );
	inline void add_intro( Thy& thy, Thm const& thm, bool allow_intro = false ) {
		add_intro(thy,Intro::rule(thm),allow_intro);
	}
private:
	bool _apply_and_discharge(
		Thesis& thesis,
		Subst const& matcher,
		Intp const& rule2child,
		size_t trial,
		Intro const& intro
	) &;
	Opt<Intro> _apply_elim_result( Thy& thy, ElimRes const& res ) {
		Thm thm = thy.weaken(res.thm);
		if( log > 14 ) _log() << "applying elimination result: " << thy.pretty(thm) << std::endl;
		for( unsigned short i = 0; i < res.guards; i++ ) {
			thm = discharge(thy,thm,{});
		}
		if( res.after == 0 ) {
			if( res.mode == '=' ) {
				if( log > 4 ) _log() << "declaring simp elimination result: " << thy.pretty(thm) << std::endl;
				auto [ind,rel,rule] = thy.rewriter(SIMP).make_rule(thm,false);
				thy.add_thm(SIMP+rel,thm,{rule});
			} else if( res.mode == '?' ) {
				if( log > 4 ) _log() << "declaring weak elimination result: " << thy.pretty(thm) << std::endl;
				add_intro(thy,thm,false);
			} else {
				return {Intro::rule(thm)};
			}
		} else {
			if( log > 4 ) _log() << "declaring further elimination result: " << thy.pretty(thm) << std::endl;
			Elim::rule(thm,0,res.after,res.mode);
		}
		return {};
	}
	Opt<Thm> _apply_rewrite_rule(
		Thy const& thy,
		Rewrite::Rule const& rule,
		Subst const& matcher,
		Intp const& rule2thy,
		Opt<std::string const&> simp,
		std::vector<char>::const_iterator pos_it,
		std::vector<char>::const_iterator pos_end
	) &;
	bool _discharge(
		Thesis& thesis,
		size_t trial,
		bool fail,
		Opt<std::string const&> simp,
		size_t elim_res_ind
	) &;
	Thm _make_refl( Thy& thy, CTerm const& source, std::string const& rel ) &;
	Opt<std::pair<Thm,CTerm>> _step(
		Thy const& thy,
		CTerm const& source,
		Opt<std::string const&> simp,
		std::string const& rel,
		std::vector<char>::const_iterator it,
		std::vector<char>::const_iterator end
	) &;
	/** rewrites abstraction.
	 * @returns equation, the rhs, and whether rewrite succeeded
	 */
	bool _step_cond( Thy const& thy, Intp& intp, CTerm const& cond, bool rewrite, Opt<std::string const&> simp, std::string const& rel, std::vector<char>::const_iterator it, std::vector<char>::const_iterator end ) &;
	Opt<Thm> _steps( Thy& thy, CTerm const& source, Opt<std::string const&> simp, size_t min, size_t max, bool normalize, std::vector<char> const& pos, std::string const& rel ) &;
};

inline void Thesis::auto_discharge() & {
	auto inf = Resolver(_thy.find_rewriter(SIMP));
	inf.discharge(*this,SIMP);
}
inline Thm Thesis::discharge_all() & {
	while( _goals > 0 ) auto_discharge();
	return _thm;
}
inline Resolver Thy::resolver( char log ) const& {
	return Resolver(find_rewriter(SIMP),log);
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