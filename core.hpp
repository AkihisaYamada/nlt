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
#include"ref.hpp"
#include"string.hpp"

class Term;
class Ctxt;
class Thm;

class VarMaker {
	static std::vector<String> vec;
	unsigned int nest;
public:
	VarMaker() : nest(0) {}
	String make();
};

extern String const VOID_var;
extern String const IMP_var;
extern String const ALL_var;
extern Term const IMP;
extern Term const ALL;

typedef std::map<String,String,std::less<>> Renaming;
typedef std::map<String,Term const,std::less<>> TermMap;
typedef std::set<String,std::less<>> Syms;

std::ostream& operator<<(std::ostream& os, Syms const& syms);

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
	Term* operator&() { // making pointer is private
		return this;
	}
	Term(App const& app) : _type(APP), _un(app) {}
	Term(Abs const& abs) : _type(ABS), _un(abs) {}
	Term(Bind const& bind) : _type(BIND), _un(bind) {}
	typedef std::pair<Term const&,Term const&> Pair;
	typedef std::pair<String const&, Term const&> StrTerm;
public:
	Term(Term const& other);
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
	Term subst(String const& var, Term const& val) const {
		Renaming ren;
		return _subst(var,val,ren,val.fsyms(),VarMaker());
	}
private:
	Union _copy_un() const;
	bool _eq(Term const& r, Renaming& lmap, Renaming& rmap, VarMaker vars) const;// equality test
	void _iter_syms(
		Syms& bsyms,
		std::function<void(String const&)> const& bsym,
		std::function<void(String const&)> const& fsym
	) const;
	Term _subst(String const& var, Term const& val, Renaming& ren, Syms const& fixed, VarMaker vars) const;

	friend bool operator==(Term const& l, Term const& r) {
		Renaming lmap, rmap;
		return l._eq(r,lmap,rmap,VarMaker());
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
	Syms const& syms() const;
	std::vector<String> const& sym_list() const;
	std::optional<Ctxt> const& parent() const;
	/**
	 * @brief Returns the set of assumptions.
	 */
	std::vector<Term> const& assms() const;
	TermMap const& specs() const;
	TermMap const& thms() const;
	/**
	 * @brief tests if a symbol is fixed.
	 */
	bool fixes(String const& sym) const;
	/**
	 * @brief Fixes a symbol if it is not fixed yet.
	 */
	Ctxt const& fix(String const& sym) const;
	/**
	 * @brief Adds assumption in the context.
	 */
	Ctxt const& assume(String const& name, Term const& assm) const;
	std::pair<Term,Thm> obtain(String const& sym, Term const& spec) const;
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
	Term _thm(String const& name) const;
	void _add_thm(String const& name, Term const& stmt) const;
};

struct Ctxt::Body {
	/**
	 * @brief Parent context.
	 */
	std::optional<Ctxt> parent;
	/**
	 * @brief The set of fixed symbols in the context or ancestors.
	 */
	Syms syms;
	/**
	 * @brief The vector of those symbols that are fixed in the context, but not in ancestors.
	 */
	std::vector<String> sym_list;
	std::vector<Term> assms;
	TermMap specs; // constant specifications
	TermMap thms; // table of theorems
};

inline bool operator==(Ctxt::Body const& l, Ctxt::Body const& r) {
	return l.parent == r.parent && l.syms == r.syms && l.assms == r.assms && l.specs == r.specs && l.thms == r.thms;
};

inline Ctxt::Ctxt(std::optional<Ctxt> const& parent) : _ref(Ref<Ctxt::Body>(Ctxt::Body{parent})) {}

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
inline TermMap const& Ctxt::specs() const {
	return _ref->specs;
}
inline TermMap const& Ctxt::thms() const {
	return _ref->thms;
}
inline Ctxt const& Ctxt::assume(String const& name, Term const& assm) const {
	_ref->assms.push_back(assm);
	_add_thm(name,assm);
	return *this;
}

inline bool operator!=(Ctxt const& l, Ctxt const& r) {
	return !(l == r);
}

class Thm : public Term {
private:
	Ctxt _ctxt;
	/**
	 * @brief Trusted construction of Thm. This being private is crucial.
	 */
	Thm(Ctxt const& ctxt, Term const& claim) : _ctxt(ctxt), Term(claim) {}
	Thm() = delete;
	Thm* operator&() = delete;
public:
	Thm& operator=(Thm const& other) {
		_ctxt = other._ctxt;
		this->Term::operator=(other);
		return *this;
	}
	/**
	 * @brief The context the theorem is from
	 */
	Ctxt const& ctxt() const {
		return _ctxt;
	}
	/**
	 * @brief forall elimination. This theorem must be of form ∀x. P(x).
	 * @return Thm P(t)
	 * @exception MalformedInstantiation
	 */
	Thm instantiate(Term const& t) const;
	/**
	 * @brief implication elimination. This theorem must be of form P ⟹ Q.
	 * 
	 * @param t must be alpha equal to P.
	 * @return Thm Q.
	 * @exception MalformedDischarge
	 * @exception WrongContext
	 */
	Thm discharge(Thm const& t) const;
	/**
	 * @brief Moves the theorem to ancestor context.
	 * Context-bound symbols will be universally quantified,
	 * and assumptions are made into implication.
	 */
	Thm lift(Ctxt const& ctxt) const;
	/**
	 * @brief Imports the theorem to descendant context.
	 * 
	 * @param ctxt the descendant context.
	 * @return Thm 
	 */
	Thm adopt(Ctxt const& ctxt) const;
private:
	friend Thm Ctxt::thm(String const& name) const;
	friend std::pair<Term,Thm> Ctxt::obtain(String const& sym, Term const& spec) const;
};

inline Thm Ctxt::thm(String const& name) const {
	return Thm(*this,_thm(name));
}

inline Ctxt const& Ctxt::claim(String const& name, Thm const& thm) const {
	Thm thm_here = thm.lift(*this);
	_add_thm(name,thm_here);
	return *this;
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


#endif
