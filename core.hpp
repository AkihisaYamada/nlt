#ifndef _CORE_HPP_
#define _CORE_HPP_

#include<cassert>
#include<map>
#include<cstring>
#include<string>
#include<vector>
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

extern Term const IMP;
extern Term const ALL;

typedef map<string,string,less<>> Renaming;
typedef map<string,Term const,less<>> TermMap;
typedef set<string,less<>> Syms;

ostream& operator<<(ostream& os, Syms const& syms);

class Term {
	struct VarMaker {
		static vector<string_view> vec;
		unsigned int nest;
		VarMaker() : nest(0) {}
		string_view make();
	};
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
		Union(Ref<string const> sym) : sym(sym) {}
		Union(Ref<App const> const& app) : app(app) {}
		Union(Ref<Abs const> const& abs) : abs(abs) {}
		Union(Ref<Bind const> const& fix) : fix(fix) {}
	} _un;
	Term() = delete; // uninitialized constructor is not allowed
	Term* operator&() { // making pointer is private
		return this;
	}
	Term(Term const& fun, Term const& arg); // application
	Term(string_view var, Term const& body); // abstraction
	Term(string_view binder, Term const& val, void*); // binding
public:
	/**
	 * @brief Constructs a symbol term
	 */
	Term(string_view sym) : _type(SYM), _un(string(sym)) {}
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
	string const* sym() const {
		return _type == SYM ? &*_un.sym : NULL;
	}
	App const* app() const;
	Abs const* abs() const;
	Bind const* fix() const;
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

inline Term::App const* Term::app() const {
	return _type == APP ? &*_un.app : NULL;
}
inline Term::Abs const* Term::abs() const {
	return _type == ABS ? &*_un.abs : NULL;
}
inline Term::Bind const* Term::fix() const {
	return _type == BIND ? &*_un.fix : NULL;
}
inline string_view rename_sym(Renaming const& map, string_view sym) {
	auto it = map.find(sym);
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
	Syms const syms() const;
	vector<string> const& sym_list() const;
	optional<Ctxt> const& parent() const;
	/**
	 * @brief Returns the set of assumptions.
	 */
	vector<Term> const& assms() const;
	TermMap const thms() const;
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
	void _quantify_thm(Ctxt const& other, Term& stmt) const;
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
	TermMap thms; // table of theorems
};

inline Ctxt::Ctxt(optional<Ctxt> const& parent) : _ref(Ref(Ctxt::Body{parent})) {}

inline Syms const Ctxt::syms() const {
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
inline TermMap const Ctxt::thms() const {
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
	Thm lift() const;
private:
	Ctxt _ctxt;
	/**
	 * @brief Trusted construction of Thm. This being private is crucial.
	 */
	Thm(Ctxt const& ctxt, Term const& claim) : _ctxt(ctxt), Term(claim) {}
	Thm() = delete;
	Thm* operator&() = delete;
	friend Thm Ctxt::thm(string_view name) const;
};
inline Thm Ctxt::thm(string_view name) const {
	return Thm(*this,_thm(name));
}
inline Ctxt const& Ctxt::claim(string_view name, Thm const& thm) const {
	Term stmt = thm;
	_quantify_thm(thm.ctxt(),stmt);
	_add_thm(name,stmt);
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

ostream& operator<<(ostream& os, Term const& t);
ostream& operator<<(ostream& os, Ctxt const& ctxt);
ostream& operator<<(ostream& os, Thm const& t);

#endif
