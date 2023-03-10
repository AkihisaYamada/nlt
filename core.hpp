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
#include<variant>
#include"ref.hpp"
#include"string.hpp"

class Term;
class Ctxt;
class Thm;
class CTerm;
class CSubst;

/**
 * @brief flags if unproved claims are made
 */
static bool polluted;

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

typedef std::set<String,std::less<>> StrSet;

class Term {
	template<typename T>
	struct Opt {
		T* ptr;
		operator bool() const { return ptr; }
		T& operator*() { return *ptr; }
		T* operator->() { return ptr; }
	};
	struct App : Ref<std::pair<Term,Term> const> {
		 App(Term const& fun, Term const& arg) : Ref({fun,arg}) {}
	};
	struct Abs : Ref<std::pair<String,Term> const> {
		Abs(String const& var, Term const& body) : Ref({var,body}) {}
	};
	struct Bind : Ref<std::pair<String,Term> const> {
		Bind(String const& var, Term const& val) : Ref({var,val}) {}
	};
	std::variant<String,App,Abs,Bind> _un;
	Term(App const& app) : _un(app) {}
	Term(Abs const& abs) : _un(abs) {}
	Term(Bind const& bind) : _un(bind) {}
	typedef std::pair<Term const&,Term const&> Pair;
	typedef std::pair<String const&, Term const&> StrTerm;
public:
	/**
	 * @brief Construct a symbol term
	 */
	Term(String const& sym = VOID_var) : _un(sym) {}
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
	Opt<String const> sym() const {
		return {std::get_if<String>(&_un)};
	}
	Opt<std::pair<Term,Term> const> app() const {
		auto ptr = std::get_if<App>(&_un);
		return { ptr ? &**ptr : nullptr };
	}
	Opt<std::pair<String,Term> const> abs() const {
		auto ptr = std::get_if<Abs>(&_un);
		return { ptr ? &**ptr : nullptr };
	}
	Opt<std::pair<String,Term> const> fix() const {
		auto ptr = std::get_if<Bind>(&_un);
		return { ptr ? &**ptr : nullptr };
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
		StrSet bsyms;
		_iter_syms(bsyms,bsym,fsym);
	}
	StrSet fsyms() const;
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
	 * @param f the mapping applied on free variables.
	 * @param fixed flags fixed variables.
	 * @return Term 
	 */
	Term map(std::function<Term(String const&)> f, std::function<bool(String const&)> fixed) const {
		StrMap<String> bsyms;
		return _map(f,fixed,bsyms);
	};
private:
	void _iter_syms(
		StrSet& bsyms,
		std::function<void(String const&)> const& bsym,
		std::function<void(String const&)> const& fsym
	) const;
	Term _map(std::function<Term(String const&)> f, std::function<bool(String const&)> fixed, StrMap<String>& bsyms) const;
	static bool _eq(Term const& l, Term const& r, StrMap<unsigned int>& lmap, StrMap<unsigned int>& rmap, unsigned int depth);// equality test

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
	Ctxt();
public:
	Ctxt(Ctxt const& other) : _ref(other._ref) {}
	/**
	 * @brief The root Ctxt
	 */
	static Ctxt root() {
		return Ctxt();
	}
	/**
	 * @brief Finds the parent or child context.
	 */
	std::optional<Ctxt const> find_ctxt(String const& name = String()) const;
	/**
	 * @brief Obtains the parent or child context.
	 * @exception WrongContext is thrown if no such context is found.
	 */
	Ctxt ctxt(String const& name = String()) const;
	/**
	 * @brief Ensures that this has the given context as an ancestor.
	 * @exception WrongContext is thrown if it does not.
	 */
	void ensure_ancestor(Ctxt const& ancestor) const {
		for( Ctxt cur = *this; cur != ancestor; cur = cur.ctxt() );
	}
	/**
	 * @brief The set of locally fixed variables.
	 */
	StrSet const& fvars() const;
	/**
	 * @brief The sequence of locally fixed variables.
	 */
	std::vector<String> const& fvar_list() const;
	/**
	 * @brief The set of locally obtained constants and their specifications
	 */
	StrMap<std::vector<std::pair<String,Term>>> const& specs() const;
	/**
	 * @brief The sequence of local assumptions.
	 */
	std::vector<Term> const& assms() const;
	/**
	 * @brief Local theorems.
	 * 
	 * @return map from the theorem names to the statements.
	 */
	StrMap<Term const> const& thms() const;
	/**
	 * @brief finds a symbol if it is locally fixed.
	 */
	std::optional<String const> find_sym_local(String const& sym) const;
	/**
	 * @brief finds a symbol fixed in this or ancestor contexts.
	 */
	std::optional<String const> find_sym(String const& sym) const;
	/**
	 * @brief Fixes a symbol if it is not fixed yet.
	 */
	CTerm fix(String const& sym);
	/**
	 * @brief Adds assumption in the context.
	 */
	Thm assume(String const& name, Term const& assm);
	/**
	 * @brief Fixes a symbol with a specification.
	 * the existence of sym that satisfy spec
	 *
	 * @param sym the symbol to be fixed.
	 * @param specs the specification of the symbol.
	 * @return first element the goal stating the existence of such sym,
	 * and the second is Ctxt assuming the existence and having specs as theorems.
	 */
	std::pair<CTerm,Ctxt const> obtain(String const& sym, std::vector<std::pair<String,Term>> const& specs);
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
	 * @brief Adds a named theorem in the context.
	 * @exception WrongContext is thrown if the theorem doesn't belong to this or an ancestor
	 */
	Ctxt& claim(String const& name, Thm const& thm);
	/**
	 * @brief Returns the n-th assumption.
	 */
	Thm assm(size_t n) const;
	/**
	 * @brief Obtains a named theorem from the context or an ancestor.
	 * @exception TheoremNotFound is thrown if the name doesn't match any.
	 */
	Thm thm(String const& name) const;
	/**
	 * @brief Creates a child context.
	 */
	Ctxt branch() const;
	/**
	 * @brief locale interpretation.
	 * 
	 * @param subst closed substitution of the parent context
	 * @param thms proofs of the assumptions, in the parent context
	 * @return the result context with no bound variable
	 */
	Ctxt interpret(CSubst const& subst, std::vector<Thm> const& thms) const;

	/**
	 * @brief Imports another context.
	 * 
	 * @param ctxt target to be imported. Its parent must be a direct ancestor of the current context.
	 * @return this
	 */
	Ctxt& import(Ctxt const& ctxt);

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
	 * @brief Context directory.
	 */
	StrMap<Ctxt const> ctxts;
	/**
	 * @brief The set of locally fixed variables (excluding ancestors).
	 */
	StrSet fvars;
	/**
	 * @brief The vector of locally fixed variables.
	 */
	std::vector<String> fvar_list;
	/**
	 * @brief Locally obtained constants and their specifications.
	 */
	StrMap<std::vector<std::pair<String,Term>>> specs;
	std::vector<Term> assms;
	StrMap<Term const> thms; // table of theorems
};

/**
 * @brief dummy: Contexts are equal only if they have the same reference to the body.
 * Therefore, two context bodies are always considered unequal.
 */
inline bool operator==(Ctxt::Body const& l, Ctxt::Body const& r) {
	return false;
};

inline Ctxt::Ctxt() : _ref(Body()) {};

inline Ctxt Ctxt::branch() const {
	Ctxt ret;
	ret._ref->ctxts.insert({"",*this});
	return ret;
}

inline StrSet const& Ctxt::fvars() const {
	return _ref->fvars;
}
inline std::vector<String> const& Ctxt::fvar_list() const {
	return _ref->fvar_list;
}
inline StrMap<std::vector<std::pair<String,Term>>> const& Ctxt::specs() const {
	return _ref->specs;
}

inline Ctxt Ctxt::ctxt(String const& name) const {
	auto const& it = _ref->ctxts.find(name);
	if( it == _ref->ctxts.end() ) {
		throw WrongContext();
	}
	return it->second;
}
inline std::optional<Ctxt const> Ctxt::find_ctxt(String const& name) const {
	auto const& it = _ref->ctxts.find(name);
	if( it == _ref->ctxts.end() ) {
		return std::optional<Ctxt>();
	}
	return it->second;
}
inline std::vector<Term> const& Ctxt::assms() const {
	return _ref->assms;
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
		auto tapp = Term::app();
		return tapp ? Pair(CTerm(_ctxt,tapp->first),CTerm(_ctxt,tapp->second)) : std::optional<Pair>();
	}
	/**
	 * @brief Deconstruct closed abstraction.
	 * 
	 * @return If this is an abstraction, the pair of the bound variable and the body, belonging to a new context that fixes the bound variable.
	 */
	std::optional<StrTerm> abs() const;
	std::optional<StrTerm> fix() const {
		auto tfix = Term::fix();
		return tfix ? StrTerm(tfix->first,CTerm(_ctxt,tfix->second)) : std::optional<StrTerm>();
	}
	/**
	 * @brief Application of closed terms. Both terms should belong to the same context.
	 */
	CTerm operator()(CTerm const& arg) const {
		if( _ctxt != arg._ctxt ) {
			throw WrongContext();
		}
		return CTerm(_ctxt,Term::operator()(arg));
	}
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
	 * @brief Applies a closed substitution to a closed term.
	 * 
	 * @param subst a substitution in an ancestor context.
	 * @return the instance, closed with respect to the ancestor.
	 */
	CTerm subst(CSubst const& subst) const;

	/**
	 * @brief instantiates the bound variable. This must be an abstraction.
	 * 
	 * @param arg
	 * @return CTerm 
	 */
	CTerm inst(CTerm const& arg) const {
		auto a = Term::abs();
		if( !a ) {
			throw MalformedInstantiation(*this,arg);
		}
		return CTerm(_ctxt,a->second.subst(a->first,arg));
	}
	/**
	 * @brief Moves a closed term to a descendant context
	 * 
	 * @param ctxt the descendant context
	 * @return CTerm 
	 */
	CTerm weaken(Ctxt const& ctxt) const {
		ctxt.ensure_ancestor(_ctxt);
		return CTerm(ctxt,*this);
	}

	/**
	 * @brief Lifts a closed term to one with respect to the parent context.
	 *   Symbols fixed in the context will be abstracted.
	 * @return the closed term with respect to the parent.
	 */
	CTerm lift() const;

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
	 * @brief The context in which the range of the substitution is closed.
	 */
	Ctxt const& ctxt() const {
		return _ctxt;
	}
	/**
	 * @brief The map from variable names to the substitutes.
	 * 
	 * @return StrMap<Term> const& 
	 */
	StrMap<Term> const& map() const {
		return _map;
	}
	/**
	 * @brief (re)assigns a value to a variable
	 */
	CSubst& assign(String const& var, Term const& val) {
		return _assign(var,_ctxt.enclose(val));
	}
	void erase(String const& var) {
		_map.erase(var);
	}
	/**
	 * @brief (re)assigns a value to a variable
	 */
	CSubst& assign(String const& var, CTerm const& val) {
		return _assign(var,val.subst(_ctxt));// val should be also closed wrt ctxt
	}
	std::optional<CTerm> get(String const& var) const {
		auto it = _map.find(var);
		return it == _map.end() ? std::optional<CTerm>() : CTerm(_ctxt,it->second);
	}
private:
	CSubst& _assign(String const& var, CTerm const& val);
};

inline Term Term::subst(String const& var, Term const& val) const {
	return subst(CSubst(Ctxt::root()).assign(var,val));
}

class Thm : public CTerm {
private:
	/**
	 * @brief Trusted construction of Thm. This being private is crucial.
	 */
	Thm(CTerm const& t) : CTerm(t) {}
	Thm() = delete;
	Thm* operator&() = delete;
	Thm _allE(CTerm const& t) const;
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
	Thm allE(Term const& t) const {
		return _allE(_ctxt.cterm(t));
	}
	Thm allE(CTerm const& t) const {
		if( t._ctxt != _ctxt ) {
			throw WrongContext();
		}
		return _allE(t);
	}
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
	 * @brief Moves the theorem to the parent context.
	 * Context-bound symbols will be universally quantified,
	 * and assumptions are made into implication.
	 */
	Thm intro() const;
	/**
	 * @brief Moves the theorem to a descendant context.
	 * 
	 * @param ctxt the descendant context.
	 * @return Thm 
	 */
	Thm weaken(Ctxt const& ctxt) const {
		return CTerm::weaken(ctxt);
	}
	friend Ctxt;
	friend Thm sorry(CTerm const&);
};

inline Thm Ctxt::thm(String const& name) const {
	return CTerm(*this,_thm(name));
}
inline Thm Ctxt::assm(size_t n) const {
	if( n > assms().size() ) {
		throw TheoremNotFound("$assm "+std::to_string(n));
	}
	return CTerm(*this,_ref->assms[n]);
}
inline Thm Ctxt::assume(String const& name, Term const& assm) {
	CTerm const& t = enclose(assm);
	_ref->assms.push_back(assm);
	_ref->thms.insert({name,assm});
	return t;
}
inline Ctxt& Ctxt::claim(String const& name, Thm const& thm) {
	if( thm._ctxt != *this ) {
		throw WrongContext();
	}
	_ref->thms.insert({name,thm});
	return *this;
}
/**
 * @brief The unsound way of obtaining a theorem.
 */
inline Thm sorry(CTerm const& t) {
	polluted = true;
	return Thm(t);
}

// workaround for Visual Studio...?
//template<> inline constexpr bool std::is_nothrow_constructible_v<Ctxt,Ctxt&> = true;

#endif
