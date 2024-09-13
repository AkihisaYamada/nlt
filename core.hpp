#ifndef _CORE_HPP_
#define _CORE_HPP_

#include<cassert>
#include<string>
#include<vector>
#include<set>
#include<exception>
#include<functional>
#include<list>
#include"ref.hpp"
#include"sum.hpp"
#include"map.hpp"

#define ALL_char '∀'
#define IMP_char '⟹'

class Term;
class Ctxt;
class Thm;
class CTerm;
class CSubst;
class Intp;

/** @brief flags if unproved claims are made */
static bool polluted;

/** @brief renames a variable so that it is not in the set of symbols.
 * 
 * @param var variable to be made fresh
 * @param test avoided names
 */
std::string avoid(std::string const& var, std::function<bool(std::string const&)> const& test);

extern std::string const VOID_var;
extern std::string const IMP_var;
extern std::string const ALL_var;
extern Term const IMP;
extern Term const ALL;
std::ostream& operator<<(std::ostream& os, Term const& t);

template<typename T>
using StrMap = Map<std::string,T>;

typedef std::set<std::string,std::less<>> StrSet;
typedef std::multiset<std::string,std::less<>> StrMSet;

class Term {
	typedef std::pair<Term,Term> Pair;
	typedef std::pair<std::string,Term> StrTerm;
	struct App : Ref<Pair const> {
		App(Term const& fun, Term const& arg) : Ref(Ref<Pair const>::make(fun,arg)) {}
	};
	struct Abs : Ref<StrTerm const> {
		Abs(std::string const& var, Term const& body) : Ref(Ref<StrTerm const>::make(var,body)) {}
	};
	struct Bind : Ref<StrTerm const> {
		Bind(std::string const& var, Term const& val) : Ref(Ref<StrTerm const>::make(var,val)) {}
	};
	Sum<std::string,App,Abs,Bind> _un;
	Term(App const& app) : _un(app) {}
	Term(Abs const& abs) : _un(abs) {}
	Term(Bind const& bind) : _un(bind) {}
public:
	Term() {}
	~Term() {
/*		bool fl = false;
		if( auto s = std::get_if<std::string>(&_un) ) {
			fl = s->last();
		} else if( auto s = std::get_if<App>(&_un) ) {
			fl = s->last();
		} else if(  auto s = std::get_if<Abs>(&_un) ) {
			fl = s->last();
		} else if(  auto s = std::get_if<Bind>(&_un) ) {
			fl = s->last();
		} else {
		}
		if( fl ) {
			std::cerr << "Deleting " << *this << std::endl;
		}
*/	}
	/** @brief Construct a symbol term */
	Term(std::string const& sym) : _un(sym) {}
	/** @brief application */
	Term operator()(Term const& arg) const {
		return Term(App{*this,arg});
	}
	/** @brief abstraction */
	friend Term operator/=(std::string const& var, Term const& body) {
		return Term(Abs{var,body});
	}
	/** @brief binding
	 * 
	 * @param binder 
	 * @param val 
	 * @return Term 
	 */
	friend Term operator/(std::string const& binder, Term const& val) {
		return Term(Bind{binder,val});
	}
	/** @brief Copy the string if the term is a symbol. */
	Opt<std::string> sym() && {
		return std::move(_un).ref<std::string>();
	}
	/** @brief Reference to the string if the term a symbol. */
	Opt<std::string const&> sym() const & {
		return _un.ref<std::string>();
	}
	/** @brief Copy the function and argument if the term is an application. */
	Opt<Pair> app() && {
		if( auto const& opt = std::move(_un).ref<App>() ) {
			return **opt;
		}
		return {};
	}
	/** @brief Reference to the function and argument if the term is an application. */
	Opt<Pair const&> app() const & {
		if( auto opt = _un.ref<App>() ) {
			return **opt;
		}
		return {};
	}
	/** @brief Copy of the variable and body if the term is an abstraction. */
	Opt<StrTerm> abs() && {
		if( auto const& opt = std::move(_un).ref<Abs>() ) {
			return **opt;
		}
		return {};
	}
	/** @brief Reference to the variable and body if the term is an abstraction. */
	Opt<StrTerm const &> abs() const & {
		if( auto opt = _un.ref<Abs>() ) {
			return **opt;
		}
		return {};
	}
	/** @brief Copy the variable and body if the term is a binding. */
	Opt<StrTerm> fix() && {
		if( auto const& opt = std::move(_un).ref<Bind>() ) {
			return **opt;
		}
		return {};
	}
	/** @brief Reference to the variable and body if the term is a binding. */
	Opt<StrTerm const &> fix() const & {
		if( auto opt = _un.ref<Bind>() ) {
			return **opt;
		}
		return {};
	}
	/** @brief Decompose binders.
	 * @param b expected binder (quantifier)
	 */
	Opt<StrTerm const&> binder(Term const& b) const & {
		if( auto opt1 = app() ) {
			if( opt1->first == b ) {
				return opt1->second.abs();
			}
		}
		return {};
	}
	/** @brief Decompose binders.
	 * @param b expected binder (quantifier)
	 */
	Opt<StrTerm> binder(Term const& b) && {
		if( auto opt = binder(b) ) {
			return std::move(*opt);
		}
		return {};
	}
	/** @brief Decompose unary function.
	 * 
	 * @param f expected function
	 * @return the argument, if matches
	 */
	Opt<Term const&> unary(Term const& f) const & {
		if( auto opt = app() ) {
			if( opt->first == f ) {
				return opt->second;
			}
		}
		return {};
	}
	/** @brief Decompose unary function.
	 * 
	 * @param f expected function
	 * @return the argument, if matches
	 */
	Opt<Term> unary(Term const& f) && {
		if( auto opt = unary(f) ) {
			return std::move(*opt);
		}
		return {};
	}
	/** @brief Decompose binary function application
	 * 
	 * @param f expected function symbol
	 * @return the pair of arguments, in case of match
	 */
	Opt<std::pair<Term const&,Term const&>> binary(Term const& f) const & {
		if( auto x = app() ) {
			if( auto a = x->first.unary(f) ) {
				return {{*a,x->second}};
			}
		}
		return {};
	}
	/** @brief Decompose binary function application
	 * 
	 * @param f expected function symbol
	 * @return the pair of arguments, in case of match
	 */
	Opt<Pair> binary(Term const& f) && {
		if( auto x = app() ) {
			if( auto a = x->first.unary(f) ) {
				return {{std::move(*a),std::move(x->second)}};
			}
		}
		return {};
	}
	/** @brief Iterates over bound and free symbols.
	 * 
	 * @param bsym operation applied on bound symbols
	 * @param fsym operation applied on free symbols
	 */
	void iter_syms(
		std::function<void(std::string const&)> const& bsym,
		std::function<void(std::string const&)> const& fsym
	) const {
		StrMSet bsyms;
		_iter_syms(bsyms,bsym,fsym);
	}
	/** @brief Iterates over free symbols
	 * 
	 * @param fsym operation applied on free symbols
	 */
	void iter_fsyms(
		std::function<void(std::string const&)> const& fsym
	) const {
		iter_syms([](std::string const&){},fsym);
	}
	/** @brief The set of free symbols */
	StrSet fsyms() const {
		StrSet ret;
		iter_fsyms([&ret](std::string const& fsym){ret.insert(fsym);});
		return ret;
	}
	bool exists_fsym(std::function<bool(std::string const&)> const& test) const {
		try {
			iter_fsyms([&](std::string const& v){ if( test(v) ) throw 0; });
			return false;
		} catch (int x) {
			return true;
		}
	}
	bool contains_fsym(std::string const& name) const {
		return exists_fsym([&](std::string const& v){ return v == name; });
	}
	bool forall_fsyms(std::function<bool(std::string const&)> const& test) const {
		return !exists_fsym([&](auto v){ return !test(v); });
	}
	/** @brief Singleton substitution */
	Term subst(std::string const& var, CTerm const& val) const;
	/** @brief applies a substitution.
	 * 
	 * @param subst
	 * @return result of substitution
	 */
	Term subst(CSubst const& subst) const;
	/** @brief Applies a closed substitution and get a closed term.
	 * 
	 * @param subst a substitution closed in a context.
	 * @return the instance, closed in the same context.
	 */
	CTerm csubst(CSubst const& subst) const;
	/** @brief homomorphic extension.
	 * 
	 * @param f the mapping applied on free variables.
	 * @param fixed flags fixed variables.
	 * @return Term 
	 */
	Term map(
		std::function<Term(std::string const&)> f,
		std::function<bool(std::string const&)> fixed = [](std::string const&){ return false; }
	) const {
		StrMap<std::string> bsyms;
		return _map(f,fixed,bsyms);
	};
private:
	void _iter_syms(
		StrMSet& bsyms,
		std::function<void(std::string const&)> const& bsym,
		std::function<void(std::string const&)> const& fsym
	) const;
	Term _map(std::function<Term(std::string const&)> f, std::function<bool(std::string const&)> fixed, StrMap<std::string>& bsyms) const;
	static bool _eq(Term const& l, Term const& r, StrMap<unsigned int>& lmap, StrMap<unsigned int>& rmap, unsigned int depth);// equality test

	friend bool operator==(Term const& l, Term const& r) {
		StrMap<unsigned int> lmap, rmap;
		return Term::_eq(l,r,lmap,rmap,0);
	}
};
inline bool operator!=(Term const& l, Term const& r) {
	return !(l == r);
}
/** implication */
inline Term operator>>=(Term const& l, Term const& r) {
	return IMP(l)(r);
}

struct Error : public std::exception {
	Term term;
	Error(Term const& term) : term(term) {}
};
struct UnexpectedTerm : public Error {
	UnexpectedTerm(Term const& term) : Error(Term("#unexpected_term")(term)) {}
};
struct MalformedInstantiation : public Error {
	MalformedInstantiation(Term const& all, Term const& arg) :
		Error(Term("#malformed_instantiation")(all)(arg)) {}
};
struct MalformedDischarge : public Error {
	MalformedDischarge(Term const& imp, Term const& arg) :
		Error(Term("#malformed_discharge")(imp)(arg)) {}
};
struct MissingProof : public Error {
	MissingProof(Term const& term) : Error(Term("#missing_proof")(term)) {}
};
struct TheoremNotFound : public Error {
	TheoremNotFound(std::string const& name) : Error(Term("#theorem_not_found")(name)) {}
};
struct WrongContext : public std::exception {
	std::string message;
	WrongContext(std::string const& msg) : message(msg) {}
};

struct DoubleFix : public Error {
	DoubleFix(std::string const& name) : Error(Term("#double_fix")(name)) {}
};

struct UnboundVariable : public Error {
	UnboundVariable(std::string const& name) : Error(Term("#unbound_variable")(name)) {}
};

struct ConstantEscape : public Error {
	ConstantEscape(std::string const& name) : Error(Term("#escape")(name)) {}
};

/** @brief Context */
class Ctxt {
private:
	struct Body;
	Ref<Body> _ref;
	Ctxt(Ref<Body>&& ref) : _ref(ref) {}
public:
	class Fix : public std::string {};
	class Assume : public Term {};
	class Obtain {
		std::string _name;
		std::vector<Term> _props;
		friend Ctxt;
	public:
		Obtain(std::string const& name, std::vector<Term>&& specs) :
			_name(name), _props(std::move(specs)) {}
		std::string const name() const {
			return _name;
		}
		std::vector<Term> const props() const {
			return _props;
		}
	};
	using Modifier = Sum<Fix,Assume,Obtain>;
	Ctxt(Ctxt const& other) : _ref(other._ref) {}
	Ctxt(Ctxt&& other) : _ref(std::move(other._ref)) {}
	/** The root Ctxt */
	Ctxt();
	/** Optionally returns the parent context. */
	Opt<Ctxt const&> find_parent() const;
	/** @brief Obtains the parent context.
	 * @exception WrongContext is thrown if no such context is found.
	 */
	Ctxt const& ctxt() const {
		auto opt = find_parent();
		if( !opt ) {
			throw WrongContext("parent of root context");
		}
		return *opt;
	}
	/** @brief Ensures that this has the given context as an ancestor.
	 * @exception WrongContext is thrown if it does not.
	 */
	void ensure_ancestor(Ctxt const& ancestor) const {
		for( Ctxt cur = *this; cur != ancestor; cur = cur.ctxt() );
	}
	/** The set of locally fixed variables. */
	StrSet const& fvars() const&;
	/** The sequence of locally fixed variables. */
	std::vector<std::string> const& fvar_list() const;
	/** Vector of modifiers */
	std::vector<Modifier> const& modifiers() const&;
	/** Revision of the context, i.e., how many modifications are made. */
	size_t revision() const& {
		return modifiers().size();
	}
	/** Tests if a variable is locally fixed. */
	bool fixes(std::string const& name) const {
		return fvars().contains(name);
	}
	/** Locally obtained constants. */
	StrSet const& consts() const&;
	/** Tests if a variable is locally specified. */
	bool specifies(std::string const& name) const {
		return consts().contains(name);
	}
	/** tests if a symbol is fixed in this or ancestor contexts. */
	bool fixed(std::string const& sym) const &;
	/** Ensures that the term is closed in this context. */
	CTerm cterm(Term const& t) const;
	/** @brief Fixes a local variable.
	 * 
	 * @param name 
	 * @return the closed term for the variable.
	 */
	CTerm fix(std::string const& name) &;
	/** @brief Adds an assumption.
	 * 
	 * @param t the assumption, which should be closed in the context.
	 * @return the assumed theorem.
	 */
	Thm assume(CTerm const& t) &;
	Thm assume(Term const& t) &;
	/** @brief Fixes a symbol with a specification.
	 *
	 * @param thm of form ∀thesis. (∀sym. spec_1 ⟹ ... ⟹ spec_n ⟹ thesis) ⟹ thesis
	 * @return theorems for the specifications.
	 */
	std::vector<Thm> obtain(Thm const& thm) &;
	
	/** @brief Creates a child context. */
	Ctxt branch() const {
		return Ctxt(Ref<Body>::make(*this));
	}
	Ctxt& operator=(Ctxt const& other)& = default;
	Ctxt& operator=(Ctxt && other)& = default;
	friend bool operator==(Ctxt const& l, Ctxt const& r) {
		return l._ref == r._ref;
	};
	friend bool operator==(Ctxt::Body const& l, Ctxt::Body const& r);
private:
	Ctxt(Opt<Ctxt> const& parent);
	Thm _assume(Term const& t) &;
};

struct Ctxt::Body {
	/** @brief Parent context. */
	Opt<Ctxt> const ctxt;
	/** Vector of modifiers */
	std::vector<Modifier> modifiers;
	/** @brief The vector of locally fixed variables. */
	std::vector<std::string> fvars;
	/** @brief The vector of local assumptions (axioms) */
	std::vector<Term> assms;
	/** @brief The set of locally fixed variables (excluding ancestors). */
	StrSet fvar_set;
	/** @brief Locally obtained constants and their specifications. */
	StrSet constants;
};

/** @brief dummy: Contexts are equal only if they have the same reference to the body.
 * Therefore, two context bodies are always considered unequal.
 */
inline bool operator==(Ctxt::Body const& l, Ctxt::Body const& r) {
	return false;
};

inline Opt<Ctxt const&> Ctxt::find_parent() const {
	if( _ref->ctxt ) {
		return *_ref->ctxt;
	}
	return {};
}
inline std::vector<Ctxt::Modifier> const& Ctxt::modifiers() const& {
	return _ref->modifiers;
}

inline StrSet const& Ctxt::fvars() const& {
	return _ref->fvar_set;
}
inline std::vector<std::string> const& Ctxt::fvar_list() const {
	return _ref->fvars;
}
inline StrSet const& Ctxt::consts() const& {
	return _ref->constants;
}
inline bool operator!=(Ctxt const& l, Ctxt const& r) {
	return !(l == r);
}

/** @brief closed terms with respect to a context
 * 
 */
class CTerm : public Term {
private:
	Ctxt _ctxt;
	/** @brief Trusted construction of a closed term. */
	CTerm(Ctxt const& ctxt, Term const& t) : _ctxt(ctxt), Term(t) {}
	CTerm() = delete;
	CTerm* operator&() = delete;
	typedef std::pair<CTerm const, CTerm const> Pair;
	typedef std::pair<std::string const, CTerm const> StrTerm;
public:
	CTerm(CTerm const& other) : _ctxt(other._ctxt), Term(other) {}
	CTerm(CTerm&& other) : _ctxt(other._ctxt), Term(other) {}
	CTerm& operator=(CTerm const& other) {
		_ctxt = other._ctxt;
		Term::operator=((Term)other);
		return *this;
	}
	/** The context the term is from */
	Ctxt const& ctxt() const & {
		return _ctxt;
	}
	/** @brief Decompose closed application.
	 * 
	 * @return a pair of closed terms if this is an application.
	 */
	Opt<Pair> capp() const {
		if( auto tapp = Term::app() ) {
			return Pair(CTerm(_ctxt,tapp->first),CTerm(_ctxt,tapp->second));
		}
		return {};
	}
	/** @brief Decompose closed abstraction.
	 * 
	 * @return If this is an abstraction, the pair of the bound variable and the body, belonging to a new context that fixes the bound variable.
	 */
	Opt<StrTerm> cabs() const;
	/** @brief Decompose closed binders
	 * 
	 * @param b the binder
	 * @return If this is binding, the pair of the bound variable and the body, belonging to a new context that fixes the bound variable.
	 */
	Opt<StrTerm> cbinder(Term const& b) const {
		if( auto app = capp() ) {
			if( app->first == b ) {
				return cabs();
			}
		}
		return {};
	}
	/** @brief Decompose closed binary operation
	 * 
	 * @param f the binary function
	 * @return If this is application of f, then the pair of arguments.
	 */
	Opt<Pair> cbinary(Term const& f) const {
		if( auto bin = binary(f) ) {
			auto [s,t] = *bin;
			return Pair(CTerm(_ctxt,s),CTerm(_ctxt,t));
		}
		return {};
	}
	/** @brief Decompose closed fix
	 * 
	 * @return Opt<StrTerm> 
	 */
	Opt<std::tuple<std::string const, CTerm const, CTerm const>> cfix() const {
		if( auto tfix = Term::fix() ) {
			auto [v,b] = *tfix;
			return std::tuple(v,CTerm(_ctxt,v),CTerm(_ctxt,b));
		}
		return {};
	}
	/** @brief Application of closed terms. Both terms should belong to the same context.
	 */
	CTerm operator()(CTerm const& arg) const {
		if( _ctxt != arg._ctxt ) {
			throw WrongContext("applying terms of different contexts");
		}
		return CTerm(_ctxt,Term::operator()(arg));
	}
	/** @brief instantiates the bound variable. This must be an abstraction.
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
	/** @brief Moves a closed term to a descendant context
	 * 
	 * @param ctxt the descendant context
	 * @return CTerm 
	 */
	CTerm weaken(Ctxt const& ctxt) const {
		ctxt.ensure_ancestor(_ctxt);
		return CTerm(ctxt,*this);
	}
	/** @brief Lifts a closed term to one with respect to the parent context.
	 *   Symbols fixed in the context will be abstracted.
	 * @return the closed term with respect to the parent.
	 */
	CTerm lift() const;
	/** @brief Lifts a closed term to one with respect to the parent context.
	 * 
	 * @param subst a substitution in the parent context.
	 * @return the instance, closed with respect to the parent.
	 */
	CTerm lift(CSubst const& subst) const;
	friend Term;
	friend Thm;
	friend Ctxt;
	friend Intp;
	friend CSubst;
	friend bool operator==(CTerm const& l, CTerm const& r) {
		return l._ctxt == r._ctxt && (Term)l == (Term)r;
	}
};
inline bool operator!=(CTerm const& l, CTerm const& r) {
	return !(l == r);
};

/** @brief Substitution, whose range is closed with respect to a context. */
class CSubst {
private:
	StrMap<Term> _map;
	Ctxt _ctxt;
public:
	CSubst(Ctxt const& ctxt) : _ctxt(ctxt) {}
	/** @brief The context in which the range of the substitution is closed. */
	Ctxt const& ctxt() const {
		return _ctxt;
	}
	/** @brief The map from variable names to the substitutes.
	 * 
	 * @return StrMap<Term> const& 
	 */
	StrMap<Term> const& map() const {
		return _map;
	}
	/** @brief Tests if the substitution domain contains a variable. */
	bool contains(std::string const& var) const {
		return _map.contains(var);
	}
	/** @brief Tests if a variable is substituted or fixed in the context. */
	bool closes(std::string const& var) const {
		return contains(var) || _ctxt.fixed(var);
	}
	void erase(std::string const& var) {
		_map.erase(var);
	}
	bool empty() const {
		return _map.empty();
	}
	/** @brief (re)assigns a value to a variable */
	CSubst& assign(std::string const& var, CTerm const& val) {
		return _assign(var,val.csubst(_ctxt));// val should be also closed wrt ctxt
	}
	Opt<CTerm> get(std::string const& var) const {
		if( auto it = _map.find(var); it != _map.end() ) {
			return CTerm(_ctxt,it->second);
		}
		return {};
	}
private:
	CSubst& _assign(std::string const& var, CTerm const& val);
};

class Thm : public CTerm {
private:
	/** @brief Trusted construction of Thm. This being private is crucial. */
	Thm(CTerm const& t) : CTerm(t) {}
	Thm() = delete;
	Thm* operator&() = delete;
	Thm _allE(CTerm const& t) const;
public:
	Thm& operator=(Thm const& other) {
		CTerm::operator=(other);
		return *this;
	}
	/** @brief forall elimination. This theorem must be of form ∀x. P(x).
	 * @return Thm P(t)
	 * @exception MalformedIntpantiation
	 */
	Thm allE(Term const& t) const {
		return _allE(_ctxt.cterm(t));
	}
	Thm allE(CTerm const& t) const {
		if( t._ctxt != _ctxt ) {
			throw WrongContext("allE");
		}
		return _allE(t);
	}
	/** @brief implication elimination. This theorem must be of form P ⟹ Q.
	 * 
	 * @param t must be alpha equal to P and in the same context as this.
	 * @return Thm Q.
	 * @exception MalformedDischarge
	 * @exception WrongContext
	 */
	Thm impE(Thm const& t) const;
	/** @brief Moves the theorem to the parent context.
	 * Context-bound symbols will be universally quantified,
	 * and assumptions are made into implication.
	 */
	Thm intro() const;
	/** @brief Moves the theorem to a descendant context.
	 * 
	 * @param ctxt the descendant context.
	 * @return Thm 
	 */
	Thm weaken(Ctxt const& ctxt) const {
		return CTerm::weaken(ctxt);
	}
	friend Ctxt;
	friend Intp;
	friend Thm sorry(CTerm const&);
};
/** @brief The unsound way of obtaining a theorem. */
inline Thm sorry(CTerm const& t) {
	polluted = true;
	return Thm(t);
}
/** @brief Interpreter, translates facts of a context into the context it belongs. */
class Intp {
	/** @brief Instantiation of the symbols of the source context, closed in the target context. */
	CSubst _subst;
	Ctxt _src;// the source context
	int _rev;// supported revision of the source
	Intp(Ctxt const& src, Ctxt const& tgt) : _subst(tgt), _src(src), _rev(0) {}
public:
	/** @brief makes initial interpretation. */
	static Intp make(Ctxt const& src, Ctxt const& tgt);
	/** @brief instantiates a theorem. */
	Thm subst(Thm const& thm) const;
	/** @brief Instantiates a context variable.
	 * If the interpreted context is modified by fixing a new variable,
	 * then this method should be used to instantiate the variable.
	 * @param term 
	 */
	void import_fix(CTerm const& term);
	/** @brief Interprets an assumption.
	 * If the interpreted context is modified by an assumption,
	 * this method should be used to discharge the instantiated assumption.
	 * @param thm Proof of the instantiated assumption.
	 */
	void import_assume(Thm const& thm);
	/** @brief Interprets an obtained constant.
	 * If the interpreted context is modified by obtaining a constant,
	 * then this method should be used to instantiate the constant.
	 * @param term that should play the role of the constant.
	 * @param thms Proofs that the term satisfies the specification.
	 */
	void import_obtain(CTerm const& term, std::vector<Thm> const& thm);
	friend Ctxt;
};

// workaround for Visual Studio...?
//template<> inline constexpr bool std::is_nothrow_constructible_v<Ctxt,Ctxt&> = true;

#endif
