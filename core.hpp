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

using namespace std;

struct LessCstr {
	bool operator()(char const* l, char const* r) const {
		return strcmp(l,r) < 0;
	}
};

template<class T>
class Ref {
	struct Body {
		unsigned int nref;
		T body;
		Body() = delete;
		Body(T const& body) : nref(0), body(body) {}
	};
	Body* const ptr;
	Ref() = delete;
public:
	Ref(T const& body) : ptr(new Body(body)) {}
	Ref(Ref const& org) : ptr(org.ptr) {
		ptr->nref++;
	}
	Ref(Ref&& org) : ptr(org.ptr) {
		org.ptr = NULL;
	}
	~Ref() {
		if( ptr->nref == 0 ) {
			delete ptr;
		} else {
			ptr->nref--;
		}
	}
	T& operator*() const {
		return ptr->body;
	}
	T* operator->() const {
		return &ptr->body;
	}
};

class UnexpectedTerm : public exception {};
class MalformedInstantiation : public exception {};
class MalformedDischarge : public exception {};
class TheoremNotFound : public exception {};
class WrongContext : public exception {};

class Term;
class Ctxt;
class Thm;

extern Term const IMP;
extern Term const ALL;

typedef map<char const*, Term, LessCstr> Subst;
typedef map<char const*, char const* const, LessCstr> Renaming;
typedef set<char const*,LessCstr> Syms;

class Term {
	struct App;
	struct Abs;
	struct Fix;
	class VarMaker {
		static vector<char const*> vec;
		unsigned int nest;
	public:
		VarMaker() : nest(0) {}
		char const* make() {
			auto pre = nest;
			nest++;
			if( pre < vec.size() ) {
				return vec[pre];
			}
			char const* name = (new string("_" + to_string(nest)))->c_str();
			vec.push_back(name);
			return name;
		}
	};
public:
	typedef enum { SYM, APP, ABS, FIX } Type;
private:
	Type _type;
	union Union {
		char const* sym;
		Ref<App const> app;
		Ref<Abs const> abs;
		Ref<Fix const> fix;
		Union() {}
		~Union() {}
		Union(char const* sym) : sym(sym) {}
		Union(Ref<App const> const& app) : app(app) {}
		Union(Ref<Abs const> const& abs) : abs(abs) {}
		Union(Ref<Fix const> const& fix) : fix(fix) {}
	} _un;
	Term() = delete; // uninitialized constructor is not allowed
	Term* operator&() { // making pointer is private
		return this;
	}
	Term(Term const& fun, Term const& arg); // application
	Term(char const* var, Term const& body); // abstraction
	Term(char const* binder, Term const& val, void*); // binder
public:
	Term(char const* sym) : _type(SYM), _un(sym) {} // symbol
	Term(Term const& other) : _type(other._type), _un(other._copy_un()) {}
	~Term();
	Type type() const {
		return _type;
	}
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
	friend Term operator/=(char const* var, Term const& body) {
		return Term(var,body);
	}
	friend Term operator/(char const* binder, Term const& val) {
		return Term(binder,val,NULL);
	}
	char const* const* sym() const {
		return _type == SYM ? &_un.sym : NULL;
	}
	App const* app() const;
	Abs const* abs() const;
	Fix const* fix() const;
	/**
	 * @brief Iterates over bound and free symbols.
	 * 
	 * @param bsym applied on bound symbols
	 * @param fsym applied on free symbols
	 */
	void iter_syms(function<void(char const*)> const& bsym, function<void(char const*)> const& fsym) const {
		Syms bsyms;
		_iter_syms(bsyms,bsym,fsym);
	}
	Syms fsyms() const;
	Term subst(char const* var, Term const& val, function<bool(char const*)> const& fixed) const {
		Renaming ren;
		return _subst(var,val,ren,fixed,VarMaker());
	}
private:
	Union _copy_un() const;
	bool _eq(Term const& r, Renaming& lmap, Renaming& rmap, VarMaker vars) const;// equality test
	void _iter_syms(Syms& bsyms, function<void(char const*)> const&, function<void(char const*)> const&) const;
	Term _subst(char const* var, Term const& val, Renaming& ren, function<bool(char const*)> const& fixed, VarMaker vars) const;

	friend bool operator==(Term const& l, Term const& r) {
		Renaming lmap, rmap;
		return l._eq(r,lmap,rmap,VarMaker());
	}
};
inline bool operator!=(Term const& l, Term const& r) {
	return !(l == r);
}

struct Term::App {
	Term const fun;
	Term const arg;
};

struct Term::Abs {
	char const* const var;
	Term const body;
};

struct Term::Fix {
	char const* const var;
	Term const val;
};

inline Term::Term(Term const& fun, Term const& arg) : _type(APP), _un(App{fun,arg}) {}

inline Term::Term(char const* var, Term const& body) : _type(ABS), _un(Abs{var,body}) {};

inline Term::Term(char const* var, Term const& val, void* _) : _type(FIX), _un(Fix{var,val}) {};

inline Term::App const* Term::app() const {
	return _type == APP ? &*_un.app : NULL;
}
inline Term::Abs const* Term::abs() const {
	return _type == ABS ? &*_un.abs : NULL;
}
inline Term::Fix const* Term::fix() const {
	return _type == FIX ? &*_un.fix : NULL;
}
inline char const* rename_sym(Renaming const& map, char const* sym) {
	auto it = map.find(sym);
	return it == map.end() ? sym : it->second;
}

class Ctxt {
private:
	/**
	 * @brief The set of fixed symbols in the context or ancestors.
	 * 
	 */
	Syms _syms;
	/**
	 * @brief The vector of those symbols that are fixed in the context, but not in ancestors.
	 */
	vector<char const*> _sym_list;
	vector<Term> _assms;
	map<char const*, Term const, LessCstr> _thms; // table of theorems
	Ctxt(char const* name, Ctxt const* parent) : name(name), parent(parent) {}
	Term _thm(char const* name) const;
public:
	char const* const name;
	Ctxt const* const parent;
	/**
	 * @brief The root Ctxt
	 */
	Ctxt(char const* name);
	Syms const syms() const {
		return _syms;
	}
	vector<char const*> const sym_list() const {
		return _sym_list;
	}
	/**
	 * @brief Returns the set of assumptions.
	 */
	vector<Term> const assms() const {
		return _assms;
	}
	map<char const*, Term const, LessCstr> thms() const {
		return _thms;
	}
	/**
	 * @brief tests if a symbol is fixed.
	 */
	bool fixes(char const* sym) const;
	/**
	 * @brief Fixes a symbol if it is not fixed yet.
	 */
	Ctxt& fix(char const* sym);
	/**
	 * @brief Adds assumption in the context.
	 */
	Ctxt& assume(char const* name, Term const& assm);
	/**
	 * @brief Adds a named theorem in the context.
	 * @exception WrongContext is thrown if the theorem doesn't belong to this or an ancestor
	 */
	Ctxt& claim(char const* name, Thm const& thm);
	/**
	 * @brief Obtains a named theorem from the context or an ancestor.
	 * @exception TheoremNotFound is thrown if the name doesn't match any.
	 */
	Thm thm(char const* name) const;
	/**
	 * @brief Creates a child context.
	 * 
	 * @param name optional name
	 * @return the child Ctxt.
	 */
	Ctxt branch(char const* name = NULL) const {
		return Ctxt(name,this);
	}
};

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
	Ctxt const* ctxt() const {
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
	Ctxt const* _ctxt;
	/**
	 * @brief Trusted construction of Thm. This being private is crucial.
	 */
	Thm(Ctxt const* ctxt, Term const& claim) : _ctxt(ctxt), Term(claim) {}
	Thm() = delete;
	Thm* operator&() = delete;
	friend Thm Ctxt::thm(char const* name) const;
};
inline Thm Ctxt::thm(char const* name) const {
	return Thm(this,_thm(name));
}

inline Term operator>>=(Term const& l, Term const& r) {
	return IMP(l)(r);
}

inline Term operator%=(char const* var, Term const& body) {
	return ALL(var /= body);
}

ostream& operator<<(ostream& os, Term const& t);
ostream& operator<<(ostream& os, Ctxt const& ctxt);
ostream& operator<<(ostream& os, Thm const& t);

#endif
