#ifndef _CORE_HPP_
#define _CORE_HPP_

#include<cassert>
#include<map>
#include<string>
#include<vector>
#include<set>
#include<exception>
#include<functional>
#include<optional>
#include<list>
#include"ref.hpp"
#include"string.hpp"

class Term;
class Ctxt;
class Thm;
class CTerm;
class CSubst;

/**
 * @brief renames a variable so that it is not in the set of symbols.
 * 
 * @param var variable to be made fresh
 * @param test avoided names
 */
String avoid(String const& var, std::function<bool(String const&)> const& test);

extern String const VOID_var;
extern String const IMP_var;
extern String const ALL_var;
extern Term const IMP;
extern Term const ALL;

template<typename T>
class StrMap : public std::map<String,T,std::less<>> {};

typedef std::set<String,std::less<>> Syms;

class Term {
	enum { SYM, APP, ABS, BIND } _type;
	struct App {
		Ref<Term const> fun, arg;
	};
	struct Abs {
		String var;
		Ref<Term const> body;
	};
	struct Bind {
		String var;
		Ref<Term const> val;
	};
	union Union {
		String sym;
		App app;
		Abs abs;
		Bind fix;
		Union() {}
		~Union() {}
		Union(String const& sym) : sym(sym) {}
		Union(App const& app) : app(app) {}
		Union(Abs const& abs) : abs(abs) {}
		Union(Bind const& fix) : fix(fix) {}
	} _un;
	Term(App const& app) : _type(APP), _un(app) {}
	Term(Abs const& abs) : _type(ABS), _un(abs) {}
	Term(Bind const& bind) : _type(BIND), _un(bind) {}
	typedef std::pair<Term const&,Term const&> Pair;
	typedef std::pair<String const&, Term const&> StrTerm;
public:
	Term(Term const& other) : _type(other._type), _un(other._copy_un()) {}
	/**
	 * @brief Construct a symbol term
	 */
	Term(String const& sym = VOID_var) : _type(SYM), _un(sym) {}
	/**
	 * @brief Do not explicitly call destructor!
	 */
	~Term();
	Term& operator=(Term const& other);
	/**
	 * @brief application
	 */
	Term operator()(Term const& arg) const {
		return Term(App{*this,arg});
	}
	/**
	 * @brief abstraction
	 */
	friend Term operator/=(String const& var, Term const& body) {
		return Term(Abs{var,body});
	}
	/**
	 * @brief binding
	 * 
	 * @param binder 
	 * @param val 
	 * @return Term 
	 */
	friend Term operator/(String const& binder, Term const& val) {
		return Term(Bind{binder,val});
	}
	std::optional<String> sym() const {
		return _type == SYM ? _un.sym : std::optional<String>();
	}
	std::optional<Pair> app() const {
		return _type == APP ? Pair(*_un.app.fun,*_un.app.arg) : std::optional<Pair>();
	}
	std::optional<StrTerm> abs() const {
		return _type == ABS ? StrTerm(_un.abs.var,*_un.abs.body) : std::optional<StrTerm>();
	}
	std::optional<StrTerm> fix() const {
		return _type == BIND ? StrTerm(_un.fix.var,*_un.fix.val) : std::optional<StrTerm>();
	}
	/**
	 * @brief Expands implication.
	 * 
	 * @return The pair of the premise and conclusion, if this is an implication.
	 */
	std::optional<Pair> imp() const {
		if( _type == APP ) {
			Term const& fun1 = *_un.app.fun;
			if( fun1._type == APP ) {
				if( *fun1._un.app.fun == IMP ) {
					return Pair(*fun1._un.app.arg,*_un.app.arg);
				}
			}
		}
		return std::optional<Pair>();
	}
	/**
	 * @brief Expands universal quantification.
	 * 
	 * @return The pair of the variable and body, if this is a universal quantification.
	 */
	std::optional<StrTerm> all() const {
		if( _type == APP ) {
			if( *_un.app.fun == ALL && _un.app.arg->_type == ABS ) {
				auto& abs = _un.app.arg->_un.abs;
				return StrTerm(abs.var,*abs.body);
			}
		}
		return std::optional<StrTerm>();
	}
	/**
	 * @brief Iterates over bound and free symbols.
	 * 
	 * @param bsym applied on bound symbols
	 * @param fsym applied on free symbols
	 */
	void iter_syms(
		std::function<void(String const&)> const& bsym,
		std::function<void(String const&)> const& fsym
	) const {
		Syms bsyms;
		_iter_syms(bsyms,bsym,fsym);
	}
	Syms fsyms() const;
	Term subst(String const& var, Term const& val) const;
	/**
	 * @brief applies a substitution.
	 * 
	 * @param t 
	 * @return result of substitution
	 */
	Term subst(CSubst const& subst) const;
	/**
	 * @brief homomorphic extension.
	 * 
	 * @param f the mapping applied on free variables
	 * @param fixed 
	 * @param bsyms 
	 * @return Term 
	 */
	Term map(std::function<Term(String const&)> f, std::function<bool(String const&)> fixed, StrMap<String>& bsyms) const;
private:
	Union _copy_un() const;
	void _iter_syms(
		Syms& bsyms,
		std::function<void(String const&)> const& bsym,
		std::function<void(String const&)> const& fsym
	) const;
	static bool _eq(Term const& l, Term const& r, StrMap<unsigned int>& lmap, StrMap<unsigned int>& rmap, unsigned int depth);// equality test
	static bool _eq_var(String const& x, String const& y, StrMap<unsigned int>& lmap, StrMap<unsigned int>& rmap );

	friend bool operator==(Term const& l, Term const& r) {
		StrMap<unsigned int> lmap, rmap;
		return Term::_eq(l,r,lmap,rmap,0);
	}
};
inline bool operator!=(Term const& l, Term const& r) {
	return !(l == r);
}

inline Term operator>>=(Term const& l, Term const& r) {
	return IMP(l)(r);
}

inline Term operator%=(String const& var, Term const& body) {
	return ALL(var /= body);
}

struct UnexpectedTerm : public std::exception {
	Term term;
	UnexpectedTerm(Term const& term) : term(term) {}
};
struct MalformedInstantiation : public std::exception {
	Term all, arg;
	MalformedInstantiation(Term const& all, Term const& arg) : all(all), arg(arg) {}
};
struct MalformedDischarge : public std::exception {
	Term imp, arg;
	MalformedDischarge(Term const& imp, Term const& arg) : imp(imp), arg(arg) {}
};
struct TheoremNotFound : public std::exception {
	String name;
	TheoremNotFound(String const& name) : name(name) {}
};
class WrongContext : public std::exception {};

struct DoubleFix : public std::exception {
	String name;
	DoubleFix(String const& name) : name(name) {}
};

struct UnboundVariable : public std::exception {
	String name;
	UnboundVariable(String const& name) : name(name) {}
};

class CTerm;

class Ctxt {
private:
	struct Body;
	Ref<Body> _ref;
public:
	/**
	 * @brief The root Ctxt
	 */
	Ctxt();
	Ctxt(Ctxt const& other) : _ref(other._ref) {}
	std::optional<Ctxt> const& parent() const;
	Syms const& syms() const;
	std::vector<String> const& sym_list() const;
	/**
	 * @brief Returns the set of assumptions.
	 */
	std::vector<Term> const& assms() const;
	StrMap<Term const> const& specs() const;
	StrMap<Term const> const& thms() const;
	/**
	 * @brief finds a symbol if it is locally fixed.
	 */
	std::optional<String const> find_local(String const& sym) const;
	/**
	 * @brief finds a symbol fixed in this or ancestor contexts.
	 */
	std::optional<String const> find(String const& sym) const;
	/**
	 * @brief Fixes a symbol if it is not fixed yet.
	 */
	CTerm fix(String const& sym) const;
	/**
	 * @brief Adds assumption in the context.
	 */
	Ctxt const& assume(String const& name, Term const& assm);
	std::pair<Term,Thm> obtain(String const& sym, Term const& spec) const;
	/**
	 * @brief Fixes all free variables of a term, so that it will become a closed term.
	 * 
	 * @param t the term to be closed.
	 * @return CTerm whose context is this
	 */
	CTerm enclose(Term const& t);
	/**
	 * @brief Verifies a closed term.
	 * 
	 * @return CTerm object for t and this context.
	 */
	CTerm cterm(Term const& t) const;
	/**
	 * @brief Imports theorem from ancestor context.
	 * 
	 * @param thm 
	 * @return Thm 
	 */
	Thm adopt(Thm const& thm) const;
	/**
	 * @brief Adds a named theorem in the context.
	 * @exception WrongContext is thrown if the theorem doesn't belong to this or an ancestor
	 */
	Ctxt const& claim(String const& name, Thm const& thm) const;
	/**
	 * @brief Obtains a named theorem from the context or an ancestor.
	 * @exception TheoremNotFound is thrown if the name doesn't match any.
	 */
	Thm thm(String const& name) const;
	/**
	 * @brief Creates a child context.
	 */
	Ctxt branch() const {
		return Ctxt(std::optional(*this));
	}
	friend bool operator==(Ctxt const& l, Ctxt const& r) {
		return l._ref == r._ref;
	};
	friend bool operator==(Ctxt::Body const& l, Ctxt::Body const& r);
private:
	Ctxt(std::optional<Ctxt> const& parent);
	/**
	 * @brief Obtains the claim of a theorem, accessible from the context.
	 */
	Term _thm(String const& name) const;
};

struct Ctxt::Body {
	/**
	 * @brief Parent context.
	 */
	std::optional<Ctxt> parent;
	/**
	 * @brief The set of symbols fixed in this context, but not in ancestors.
	 */
	Syms syms;
	/**
	 * @brief The vector of symbols fixed in this context, but not in ancestors.
	 */
	std::vector<String> sym_list;
	std::vector<Term> assms;
	StrMap<Term const> specs; // constant specifications
	StrMap<Term const> thms; // table of theorems
};

inline Ctxt::Ctxt() : _ref(Body()) {};

inline bool operator==(Ctxt::Body const& l, Ctxt::Body const& r) {
	return l.parent == r.parent && l.syms == r.syms && l.assms == r.assms && l.specs == r.specs && l.thms == r.thms;
};

inline Ctxt::Ctxt(std::optional<Ctxt> const& parent) : _ref(Ref<Ctxt::Body>(Ctxt::Body{parent})) {}

/**
 * @brief The set of all symbols fixed in this context or an ancestor.
 */
inline Syms const& Ctxt::syms() const {
	return _ref->syms;
}
inline std::vector<String> const& Ctxt::sym_list() const {
	return _ref->sym_list;
}
inline std::optional<Ctxt> const& Ctxt::parent() const {
	return _ref->parent;
}
inline std::vector<Term> const& Ctxt::assms() const {
	return _ref->assms;
}
inline StrMap<Term const> const& Ctxt::specs() const {
	return _ref->specs;
}
inline StrMap<Term const> const& Ctxt::thms() const {
	return _ref->thms;
}

inline bool operator!=(Ctxt const& l, Ctxt const& r) {
	return !(l == r);
}

/**
 * @brief closed terms with respect to a context
 * 
 */
class CTerm : public Term {
private:
	Ctxt _ctxt;
	/**
	 * @brief Trusted construction of a closed term.
	 */
	CTerm(Ctxt const& ctxt, Term const& t) : _ctxt(ctxt), Term(t) {}
	CTerm() = delete;
	CTerm* operator&() = delete;
	typedef std::pair<CTerm const, CTerm const> Pair;
	typedef std::pair<String const, CTerm const> StrTerm;
public:
	CTerm& operator=(CTerm const& other) {
		_ctxt = other._ctxt;
		Term::operator=((Term)other);
		return *this;
	}
	/**
	 * @brief The context the term is from
	 */
	Ctxt const& ctxt() const {
		return _ctxt;
	}
	std::optional<Pair> app() const {
		auto const& tapp = Term::app();
		return tapp.has_value() ? Pair(CTerm(_ctxt,tapp->first),CTerm(_ctxt,tapp->second)) : std::optional<Pair>();
	}
	std::optional<StrTerm> abs() const {
		auto const& tabs = Term::abs();
		return tabs.has_value() ?StrTerm(tabs->first,CTerm(_ctxt,tabs->second)) : std::optional<StrTerm>();
	}
	std::optional<StrTerm> fix() const {
		auto const& tfix = Term::fix();
		return tfix.has_value() ? StrTerm(tfix->first,CTerm(_ctxt,tfix->second)) : std::optional<StrTerm>();
	}
	std::optional<StrTerm> all() const {
		auto const& tall = Term::all();
		return tall.has_value() ? StrTerm(tall->first,CTerm(_ctxt,tall->second)) : std::optional<StrTerm>();
	}
	std::optional<Pair> imp() const {
		auto const& timp = Term::imp();
		return timp.has_value() ? Pair(CTerm(_ctxt,timp->first),CTerm(_ctxt,timp->second)) : std::optional<Pair>();
	}
	/**
	 * @brief applies substitution to a closed term
	 * 
	 * @param subst
	 * @return result of substitution, still closed
	 */
	CTerm subst(CSubst const& subst) const;
	/**
	 * @brief single substitution
	 * 
	 * @param var 
	 * @param val must be closed with respect to the same context as this.
	 * @return CTerm 
	 */
	CTerm subst(String const& var, CTerm const& val) const {
		if( _ctxt != val._ctxt ) {
			throw WrongContext();
		}
		return CTerm(_ctxt,Term::subst(var,val));
	}
	/**
	 * @brief instantiates the bound variable. This must be an abstraction.
	 * 
	 * @param arg
	 * @return CTerm 
	 */
	CTerm inst(CTerm const& arg) const {
		auto const& a = abs();
		if( !a.has_value() ) {
			throw MalformedInstantiation(*this,arg);
		}
		return a->second.subst(a->first,arg);
	}
	/**
	 * @brief Moves a closed term to a descendant context
	 * 
	 * @param ctxt 
	 * @return CTerm 
	 */
	CTerm weaken(Ctxt const& ctxt) const;

	/**
	 * @brief Lifts a closed term to one with respect to the parent context.
	 * 
	 * @param subst a substitution in the parent context.
	 * @return the instance, closed with respect to the parent.
	 */
	CTerm lift(CSubst const& subst) const;

	friend Thm;
	friend Ctxt;
	friend CSubst;
	friend bool operator==(CTerm const& l, CTerm const& r) {
		return l._ctxt == r._ctxt && (Term)l == (Term)r;
	}
};
inline bool operator!=(CTerm const& l, CTerm const& r) {
	return !(l == r);
};
inline Ctxt const& Ctxt::assume(String const& name, Term const& assm) {
	enclose(assm);
	_ref->assms.push_back(assm);
	_ref->thms.insert({name,assm});
	return *this;
}

/**
 * @brief Substitution, whose range is closed with respect to a context.
 * 
 */
class CSubst {
private:
	StrMap<Term> _map;
	Ctxt _ctxt;
public:
	CSubst(Ctxt const& ctxt) : _ctxt(ctxt) {}
	/**
	 * @brief The context with respect to which the range of the substitution is closed.
	 */
	Ctxt const& ctxt() const {
		return _ctxt;
	}
	StrMap<Term> const& map() const {
		return _map;
	}
	/**
	 * @brief (re)assigns a value to a variable
	 */
	CSubst& assign(String const& var, Term const& val) {
		return _assign(var,_ctxt.enclose(val));
	}
	/**
	 * @brief (re)assigns a value to a variable
	 */
	CSubst& assign(String const& var, CTerm const& val) {
		if( val.ctxt() != _ctxt ) {
			throw WrongContext();
		}
		return _assign(var,val);
	}
	std::optional<CTerm> get(String const& var) const {
		auto it = _map.find(var);
		return it == _map.end() ? std::optional<CTerm>() : CTerm(_ctxt,it->second);
	}
private:
	CSubst& _assign(String const& var, CTerm const& val);
};

inline CTerm CTerm::subst(CSubst const& subst) const {
	if( subst.ctxt() != _ctxt ) {
		throw WrongContext();
	}
	return CTerm(_ctxt,Term::subst(subst));
}

inline Term Term::subst(String const& var, Term const& val) const {
	return subst(CSubst(Ctxt()).assign(var,val));
}

class Thm : public CTerm {
private:
	/**
	 * @brief Trusted construction of Thm. This being private is crucial.
	 */
	Thm(CTerm const& t) : CTerm(t) {}
	Thm() = delete;
	Thm* operator&() = delete;
public:
	Thm& operator=(Thm const& other) {
		CTerm::operator=(other);
		return *this;
	}
	/**
	 * @brief forall elimination. This theorem must be of form ∀x. P(x).
	 * @return Thm P(t)
	 * @exception MalformedInstantiation
	 */
	Thm allE(CTerm const& t) const;
	/**
	 * @brief implication elimination. This theorem must be of form P ⟹ Q.
	 * 
	 * @param t must be alpha equal to P and in the same context as this.
	 * @return Thm Q.
	 * @exception MalformedDischarge
	 * @exception WrongContext
	 */
	Thm impE(Thm const& t) const;
	/**
	 * @brief Moves the theorem to ancestor context.
	 * Context-bound symbols will be universally quantified,
	 * and assumptions are made into implication.
	 */
	Thm lift(Ctxt const& ctxt) const;
	/**
	 * @brief Moves the theorem to a descendant context.
	 * 
	 * @param ctxt the descendant context.
	 * @return Thm 
	 */
	Thm weaken(Ctxt const& ctxt) const {
		return CTerm::weaken(ctxt);
	}
private:
	friend Thm Ctxt::thm(String const& name) const;
	friend std::pair<Term,Thm> Ctxt::obtain(String const& sym, Term const& spec) const;
};

inline Thm Ctxt::thm(String const& name) const {
	return CTerm(*this,_thm(name));
}

inline Ctxt const& Ctxt::claim(String const& name, Thm const& thm) const {
	Thm thm_here = thm.lift(*this);
	_ref->thms.insert({name,thm_here});
	return *this;
}


#endif
