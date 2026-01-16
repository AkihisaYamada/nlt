#ifndef _INFERENCE_HPP
#define _INFERENCE_HPP

#include "theory.hpp"

class Blaster;

/** @brief Add concluder theorem to theory */
void add_forced( Thy&, Thm const& thm, bool allow_intro = false );

/** Class for inference */
class Thesis {
	Thy _thy;
	Thm _thm;
	CTerm _claim;
	size_t _goals;
	Thesis( Thy const& thy, Thm const& thesis, CTerm const& claim, size_t goals ) :
		_thy(thy), _thm(thesis), _claim(claim), _goals(goals) {}
	friend Blaster;
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
		_thm = _thm.discharge(thm);
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
	void apply( std::set<Intro> const& rules, size_t min, size_t max, bool safe, bool wide ) & {
		size_t suc = 0;
		_apply(rules,suc,min,max,safe,wide);
	}
	/** Automatically discharge a subgoal */
	void blast() &;
	/** Automatically discharge all subgoals */
	Thm blast_all() &;
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
	void _apply2( Subst const& matcher, Intro const& intro, Thy const& child, Intp const& rule2child ) &;
};

class Blaster {
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
	Blaster( Opt<Rewrite const&> const& rew, char log = 0, size_t fuel = 1023 ) : rew(rew), rules( rew ? rew->_refls.size() : 0 ), log(log), indent(1), fuel(fuel) {}
	bool blasts( Thesis& thesis, bool rewrite ) & {
		return _blast(thesis,1,true,rewrite,elim_res.size());
	}
	void blast( Thesis& thesis, bool rewrite ) & {
		_blast(thesis,1,false,rewrite,elim_res.size());
	}
	Thm blast_all( Thesis& thesis ) & {
		while( thesis._goals > 0 ) {
			blast(thesis,true);
		}
		return thesis._thm;
	}
	Opt<Thm> proves( Thy const& thy, CTerm const& claim, bool rewrite ) & {
		auto x = Thesis::claim_exact(thy,claim);
		if( blasts(x,rewrite) ) {
			return *x.concluding();
		}
		return {};
	}
	Thm prove( Thy const& thy, CTerm const& claim, bool rewrite ) & {
		auto x = Thesis::claim_exact(thy,claim);
		blast(x,rewrite);
		return *x.concluding();
	}
	/**
	* @brief Blasts first assumption of implication.
	* 
	* @return Thm the conclusion
	*/
	Opt<Thm> blasts( Thy const& thy, Thm const& thesis, bool rewrite ) & {
		if( auto imp = thesis.cbinary(IMP) )
		if( auto prem = proves(thy,imp->first,rewrite) ) {
			return thesis.discharge(*prem);
		}
		return {};
	}
	Thm blast( Thy const& thy, Thm const& thesis, bool rewrite ) & {
		auto imp = thesis.cbinary(IMP);
		if( !imp ) throw Error("nothing to blast")(thesis);
		return thesis.discharge(prove(thy,imp->first,rewrite));
	}
	/** declare derivable conclusions */
	void inflate( Thy& thy, Thm const& assm ) &;
	/**
	 * @brief returns a rewrite step equation for the given source term at given position.
	 * 
	 * @param source the term to be rewritten
	 * @return Opt<Thm> 
	 */
	Opt<std::pair<Thm,CTerm>> step( Thy const& thy, CTerm const& source, std::vector<char> const& pos ) & {
		return _step(thy,source,rew->_default_ind,pos.begin(),pos.end());
	}
	/** @brief applies rewriting */
	bool rewrites( Thesis& thesis, size_t min, size_t max, bool normalize, std::vector<char> const& pos, Opt<std::string> const& rel ) &;
	/** @brief Rewrites a theorem */
	Thm rewrites( Thy const& thy, Thm const& source, size_t min = 0 ) &;
	/** @brief returns a rewriting theorem */
	Thm steps( Thy const& thy, CTerm const& source, size_t min, size_t max, bool normalize, std::vector<char> const& pos, Opt<std::string> const& rel ) & {
		size_t ind = rew->get_ind(rel);
		if( auto ret = _steps(thy,source,min,max,normalize,pos,ind) ) {
			return *ret;
		}
		return _make_refl(thy,source,ind);
	}
private:
	bool _apply_blast(
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
		bool success,
		std::vector<char>::const_iterator pos_it,
		std::vector<char>::const_iterator pos_end
	) &;
	bool _blast(
		Thesis& thesis,
		size_t trial,
		bool fail,
		bool rewrite,
		size_t elim_res_ind
	) &;
	Thm _make_refl( Thy const& thy, CTerm const& source, char ind ) &;
	Opt<std::pair<Thm,CTerm>> _step( Thy const& thy, CTerm const& source, char ind, std::vector<char>::const_iterator it, std::vector<char>::const_iterator end ) &;
	/** rewrites abstraction.
	 * @returns equation, the rhs, and whether rewrite succeeded
	 */
	bool _step_cond( Thy const& thy, Intp& intp, CTerm const& cond, char ind, std::vector<char>::const_iterator it, std::vector<char>::const_iterator end, bool rewrite ) &;
	void _refl_cond( Thy const& thy, Intp& intp, CTerm const& cond, char ind ) &;
	Opt<Thm> _steps( Thy const& thy, CTerm const& source, size_t min, size_t max, bool safe, std::vector<char> const& pos, char ind ) &;
};

inline void Thesis::blast() & {
	auto inf = Blaster(_thy.rewriter());
	inf.blast(*this,true);
}
inline Thm Thesis::blast_all() & {
	while( _goals > 0 ) blast();
	return _thm;
}
inline Blaster Thy::blaster( char log ) const& {
	return Blaster(rewriter(),log);
}
inline Thm Thy::prove( CTerm const& claim, char log ) const& {
	auto b = blaster(log);
	auto thesis = Thesis::claim_exact(*this,claim);
	return b.blast_all(thesis);
}

inline std::ostream& operator<<( std::ostream& os, Thesis const& thesis ) {
	return os << thesis.thy().pretty(thesis.thm());
}
#endif