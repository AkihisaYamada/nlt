#ifndef _CORE_HPP_
#define _CORE_HPP_

#include<cassert>
#include<map>
#include<cstring>
#include<string>
#include<vector>
#include<list>
#include<set>
#include<exception>
#include<functional>
#include<iostream>
#include<optional>

using namespace std;

template<typename T>
class RefNull;

template<typename T>
class Ref {
	struct Body {
		unsigned int nref;
		T body;
		Body() : nref(0) {}
		Body(T const& body) : nref(0), body(body) {}
	};
	Body* ptr;
	Ref(Body* ptr) : ptr(ptr) {}
public:
	Ref() : ptr(new Body()) {}
	Ref(T const& body) : ptr(new Body(body)) {}
	Ref(Ref const& org) : ptr(org.ptr) {
		ptr->nref++;
	}
	~Ref() {
		if( ptr->nref == 0 ) {
			delete ptr;
		} else {
			ptr->nref--;
		}
	}
	Ref& operator=(Ref const& other) {
		this->~Ref<T>();
		ptr = other.ptr;
		ptr->nref++;
		return *this;
	}
	operator T*() const {
		return &ptr->body;
	}
	T& operator*() const {
		return ptr->body;
	}
	T* operator->() const {
		return &ptr->body;
	}
	friend RefNull<T>;
};

class Term;
class Ctxt;
class Thm;

class VarMaker {
	static vector<Ref<string const>> vec;
	unsigned int nest;
public:
	VarMaker() : nest(0) {}
	Ref<string const> make();
};

extern Ref<string const> const VOID_var;
extern Ref<string const> const IMP_var;
extern Ref<string const> const ALL_var;
extern Term const IMP;
extern Term const ALL;

typedef map<string,Ref<string const>,less<>> Renaming;
typedef map<string,Term const,less<>> TermMap;
typedef set<string,less<>> Syms;

ostream& operator<<(ostream& os, Syms const& syms);

class Term {
	enum { SYM, APP, ABS, BIND } _type;
	struct App;
	struct Abs;
	struct Bind;
	union Union {
		Ref<string const> sym;
		Ref<App const> app;
		Ref<Abs const> abs;
		Ref<Bind const> fix;
		Union() {}
		~Union() {}
		Union(Ref<string const> const& sym) : sym(sym) {}
		Union(Ref<App const> const& app) : app(app) {}
		Union(Ref<Abs const> const& abs) : abs(abs) {}
		Union(Ref<Bind const> const& fix) : fix(fix) {}
	} _un;
	Term* operator&() { // making pointer is private
		return this;
	}
	Term(Term const& fun, Term const& arg); // application
	Term(string_view var, Term const& body); // abstraction
	Term(string_view binder, Term const& val, void*); // binding
	typedef pair<Term const&,Term const&> Pair;
	typedef pair<string const&, Term const&> StrTerm;
public:
	/**
	 * @brief Construct a symbol term
	 */
	Term(Ref<string const> const& sym = VOID_var) : _type(SYM), _un(sym) {}
	Term(Term const& other) : _type(other._type), _un(other._copy_un()) {}
	/**
	 * @brief Do not explicitly call destructor!
	 */
	~Term();
	Term& operator=(Term const& other);
	/**
	 * @brief application
	 */
	Term operator()(Term const& arg) const {
		return Term(*this,arg);
	}
	/**
	 * @brief abstraction
	 */
	friend Term operator/=(string_view var, Term const& body) {
		return Term(var,body);
	}
	friend Term operator/(string_view binder, Term const& val) {
		return Term(binder,val,NULL);
	}
	optional<string_view> sym() const {
		return _type == SYM ? *_un.sym : optional<string_view>();
	}
	optional<Pair> app() const;
	optional<StrTerm> abs() const;
	optional<StrTerm> fix() const;
	/**
	 * @brief Expands implication.
	 * 
	 * @return The pair of the premise and conclusion, if this is an implication.
	 */
	optional<Pair> imp() const;
	/**
	 * @brief Expands universal quantification.
	 * 
	 * @return The pair of the variable and body, if this is a universal quantification.
	 */
	optional<StrTerm> all() const;
	/**
	 * @brief Uncurrying.
	 * 
	 * @return the pair of the root and the list of arguments.
	 */
	pair<Term const&, list<Term>> uncurry() const {
		return _uncurry(*this);
	}
	/**
	 * @brief Iterates over bound and free symbols.
	 * 
	 * @param bsym applied on bound symbols
	 * @param fsym applied on free symbols
	 */
	void iter_syms(function<void(string_view)> const& bsym, function<void(string_view)> const& fsym) const {
		Syms bsyms;
		_iter_syms(bsyms,bsym,fsym);
	}
	Syms fsyms() const;
	Term subst(string_view var, Term const& val) const {
		Renaming ren;
		return _subst(var,val,ren,val.fsyms(),VarMaker());
	}
private:
	Union _copy_un() const;
	bool _eq(Term const& r, Renaming& lmap, Renaming& rmap, VarMaker vars) const;// equality test
	static pair<Term const&, list<Term>> _uncurry(Term const&);
	void _iter_syms(Syms& bsyms, function<void(string_view)> const&, function<void(string_view)> const&) const;
	Term _subst(string_view var, Term const& val, Renaming& ren, Syms const& fixed, VarMaker vars) const;

	friend bool operator==(Term const& l, Term const& r) {
		Renaming lmap, rmap;
		return l._eq(r,lmap,rmap,VarMaker());
	}
};
inline bool operator!=(Term const& l, Term const& r) {
	return !(l == r);
}

struct Term::App {
	Term fun;
	Term arg;
};

struct Term::Abs {
	string var;
	Term body;
};

struct Term::Bind {
	string var;
	Term val;
};

inline Term::Term(Term const& fun, Term const& arg) : _type(APP), _un(App{fun,arg}) {}

inline Term::Term(string_view var, Term const& body) : _type(ABS), _un(Abs{string(var),body}) {};

inline Term::Term(string_view var, Term const& val, void* _) : _type(BIND), _un(Bind{string(var),val}) {};

inline optional<Term::Pair> Term::app() const {
	return _type == APP ? Pair(_un.app->fun,_un.app->arg) : optional<Pair>();
}
inline optional<Term::StrTerm> Term::abs() const {
	return _type == ABS ? StrTerm(_un.abs->var,_un.abs->body) : optional<StrTerm>();
}
inline optional<Term::StrTerm> Term::fix() const {
	return _type == BIND ? StrTerm(_un.fix->var,_un.fix->val) : optional<StrTerm>();
}
inline optional<Term::Pair> Term::imp() const {
	if( _type == APP ) {
		auto& app1 = *_un.app;
		if( app1.fun._type == APP ) {
			auto& app2 = *app1.fun._un.app;
			if( app2.fun == IMP ) {
				return Pair(app2.arg,app1.arg);
			}
		}
	}
	return optional<Pair>();
}
inline optional<Term::StrTerm> Term::all() const {
	if( _type == APP ) {
		auto& app = *_un.app;
		if( app.fun == ALL && app.arg._type == ABS ) {
			auto& abs = *app.arg._un.abs;
			return StrTerm(abs.var,abs.body);
		}
	}
	return optional<StrTerm>();
}


inline Ref<string const> rename_sym(Renaming const& map, Ref<string const> const& sym) {
	auto const& it = map.find(*sym);
	return it == map.end() ? sym : it->second;
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
	vector<string> const& sym_list() const;
	optional<Ctxt> const& parent() const;
	/**
	 * @brief Returns the set of assumptions.
	 */
	vector<Term> const& assms() const;
	TermMap const& specs() const;
	TermMap const& thms() const;
	/**
	 * @brief tests if a symbol is fixed.
	 */
	bool fixes(string_view sym) const;
	/**
	 * @brief Fixes a symbol if it is not fixed yet.
	 */
	Ctxt const& fix(string_view sym) const;
	/**
	 * @brief Adds assumption in the context.
	 */
	Ctxt const& assume(string_view name, Term const& assm) const;
	pair<Term,Thm> obtain(string_view sym, Term const& spec) const;
	Thm adopt(Thm const& thm) const;
	/**
	 * @brief Adds a named theorem in the context.
	 * @exception WrongContext is thrown if the theorem doesn't belong to this or an ancestor
	 */
	Ctxt const& claim(string_view name, Thm const& thm) const;
	/**
	 * @brief Obtains a named theorem from the context or an ancestor.
	 * @exception TheoremNotFound is thrown if the name doesn't match any.
	 */
	Thm thm(string_view name) const;
	/**
	 * @brief Creates a child context.
	 */
	Ctxt branch() const {
		return Ctxt(optional(*this));
	}
	friend bool operator==(Ctxt const& l, Ctxt const& r);
private:
	Ctxt(optional<Ctxt> const& parent);
	Term _thm(string_view name) const;
	void _add_thm(string_view name, Term const& stmt) const;
};

struct Ctxt::Body {
	/**
	 * @brief Parent context. Since option class of C++20 doesn't work well,
	 * root has itself as the parent.
	 */
	optional<Ctxt> parent;
	/**
	 * @brief The set of fixed symbols in the context or ancestors.
	 */
	Syms syms;
	/**
	 * @brief The vector of those symbols that are fixed in the context, but not in ancestors.
	 */
	vector<string> sym_list;
	vector<Term> assms;
	TermMap specs; // constant specifications
	TermMap thms; // table of theorems
};

inline Ctxt::Ctxt(optional<Ctxt> const& parent) : _ref(Ref(Ctxt::Body{parent})) {}

inline Syms const& Ctxt::syms() const {
	return _ref->syms;
}
inline vector<string> const& Ctxt::sym_list() const {
	return _ref->sym_list;
}
inline optional<Ctxt> const& Ctxt::parent() const {
	return _ref->parent;
}
inline vector<Term> const& Ctxt::assms() const {
	return _ref->assms;
}
inline TermMap const& Ctxt::specs() const {
	return _ref->specs;
}
inline TermMap const& Ctxt::thms() const {
	return _ref->thms;
}
inline Ctxt const& Ctxt::assume(string_view name, Term const& assm) const {
	_ref->assms.push_back(assm);
	_add_thm(name,assm);
	return *this;
}

inline bool operator==(Ctxt const& l, Ctxt const& r) {
	return l._ref == r._ref;
}

inline bool operator!=(Ctxt const& l, Ctxt const& r) {
	return !(l == r);
}

class Thm : public Term {
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
	Thm of(Term const& t) const;
	/**
	 * @brief implication elimination. This theorem must be of form P ⟹ Q.
	 * 
	 * @param t must be alpha equal to P.
	 * @return Thm Q.
	 * @exception MalformedDischarge
	 * @exception WrongContext
	 */
	Thm OF(Thm const& t) const;
	/**
	 * @brief Moves the theorem to parent context.
	 * Context-bound symbols will be universally quantified,
	 * and assumptions are made into implication.
	 */
	Thm move(Ctxt const& ctxt) const;
private:
	Ctxt _ctxt;
	/**
	 * @brief Trusted construction of Thm. This being private is crucial.
	 */
	Thm(Ctxt const& ctxt, Term const& claim) : _ctxt(ctxt), Term(claim) {}
	Thm() = delete;
	Thm* operator&() = delete;
	friend Thm Ctxt::thm(string_view name) const;
	friend pair<Term,Thm> Ctxt::obtain(string_view name, Term const& spec) const;
};
inline Thm Ctxt::thm(string_view name) const {
	return Thm(*this,_thm(name));
}

inline Ctxt const& Ctxt::claim(string_view name, Thm const& thm) const {
	Thm thm_here = thm.move(*this);
	_add_thm(name,thm_here);
	return *this;
}

inline Term operator>>=(Term const& l, Term const& r) {
	return IMP(l)(r);
}

inline Term operator%=(string_view var, Term const& body) {
	return ALL(var /= body);
}

struct UnexpectedTerm : public exception {
	Term term;
	UnexpectedTerm(Term const& term) : term(term) {}
};
struct MalformedInstantiation : public exception {
	Term all, arg;
	MalformedInstantiation(Term const& all, Term const& arg) : all(all), arg(arg) {}
};
struct MalformedDischarge : public exception {
	Term imp, arg;
	MalformedDischarge(Term const& imp, Term const& arg) : imp(imp), arg(arg) {}
};
struct TheoremNotFound : public exception {
	string name;
	TheoremNotFound(string_view name) : name(name) {}
};
class WrongContext : public exception {};

struct DoubleFix : public exception {
	string name;
	DoubleFix(string_view name) : name(name) {}
};


#endif
