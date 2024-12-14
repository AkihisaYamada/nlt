#ifndef _CORE_HPP_
#define _CORE_HPP_

#include<cassert>
#include<string>
#include<vector>
#include<set>
#include<exception>
#include<functional>
#include<list>
#include<iostream>
#include"ref.hpp"
#include"sum.hpp"
#include"map.hpp"


#define DEB(expr) do { std::cerr << __FILE__ << ":" << __LINE__ << ": " << expr << std::endl; } while(0)

#define ALL_char '∀'
#define IMP_char '⟹'

class Term;
class Ctxt;
class Thm;
class CTerm;
class CSubst;
class Intp;

/** @brief renames a variable so that it is not in the set of symbols.
 * 
 * @param var variable to be made fresh
 * @param test avoided names
 */
std::string avoid(std::string_view const& var, std::function<bool(std::string const&)> const& test);

extern std::string const VOID_var;
extern std::string const IMP;
extern std::string const ALL;
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
		Abs(std::string_view const& var, Term const& body) : Ref(Ref<StrTerm const>::make(var,body)) {}
	};
	struct Bind : Ref<StrTerm const> {
		Bind(std::string_view const& var, Term const& val) : Ref(Ref<StrTerm const>::make(var,val)) {}
	};
	Sum<std::string,App,Abs,Bind> _un;
	struct _Mapper {
		std::function<Term(std::string const&)> const& f;
		std::function<bool(std::string_view const&)> const& fixed;
		StrMap<std::string> bsyms;
		std::string rename( std::string_view const& var ) const {
			return avoid(var,[&](std::string_view const& x){ return bsyms.contains(x) || fixed(x); });
		}
		Term map_var( std::string const& sym ) {
			if( auto opt = bsyms.finds(sym) ) {
				return opt->second;
			}
			return f(sym);
		}
		Term map_abs( std::string const& var, Term body );
		Term map( Term const& t );
	};
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
	Term(std::string_view const& sym) : _un(std::string(sym)) {}
	/** @brief Construct a symbol term */
	Term(std::string&& sym) : _un(std::move(sym)) {}
	/** @brief Construct a symbol term */
	Term(char const* sym) : _un(sym) {}
	/** @brief Construct a symbol term */
	Term(std::string const& sym) : _un(sym) {}
	/** @brief application */
	Term operator()(Term const& arg) const {
		return Term(App{*this,arg});
	}
	/** @brief abstraction */
	friend Term operator/=(std::string_view const& var, Term const& body) {
		return Term(Abs{var,body});
	}
	/** @brief binding
	 * 
	 * @param binder 
	 * @param val 
	 * @return Term 
	 */
	friend Term operator%=(std::string_view const& binder, Term const& val) {
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
	Opt<StrTerm const&> binder( std::string_view const& b ) const & {
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
	Opt<StrTerm> binder( std::string_view const& b ) && {
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
	Opt<Term const&> unary( std::string_view const& f ) const & {
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
	Opt<Term> unary( std::string_view const& f ) && {
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
	Opt<std::pair<Term const&,Term const&>> binary( std::string_view const& f ) const & {
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
	Opt<Pair> binary( std::string_view const& f ) && {
		if( auto x = app() ) {
			if( auto a = x->first.unary(f) ) {
				return {{std::move(*a),std::move(x->second)}};
			}
		}
		return {};
	}
	/** @brief Iterates over bound and free symbols.
	 * 
	 * @param fsym operation applied on free symbols
	 * @param bsym operation applied on bound symbols
	 */
	void iter_syms(
		std::function<void(std::string_view const&)> const& fsym,
		std::function<void(std::string_view const&)> const& bsym = [](std::string_view const&){}
	) const {
		StrMSet bsyms;
		_iter_syms(bsyms,bsym,fsym);
	}
	/** @brief Iterates over free symbols
	 * 
	 * @param fsym operation applied on free symbols
	 */
	void iter_fsyms(
		std::function<void(std::string_view const&)> const& fsym
	) const {
		iter_syms(fsym,[](std::string_view const&){});
	}
	/** @brief The set of free symbols */
	StrSet fsyms() const {
		StrSet ret;
		iter_syms([&ret](std::string_view const& fsym){ret.emplace(fsym);});
		return ret;
	}
	bool exists_fsym(std::function<bool(std::string_view const&)> const& test) const {
		try {
			iter_syms([&](std::string_view const& v){ if( test(v) ) throw 0; });
			return false;
		} catch (int x) {
			return true;
		}
	}
	bool contains_fsym(std::string_view const& name) const {
		return exists_fsym([&](auto v){ return v == name; });
	}
	bool forall_fsyms(std::function<bool(std::string_view const&)> const& test) const {
		return !exists_fsym([&](auto v){ return !test(v); });
	}
	/** @brief Singleton substitution
	 * @param val it must be closed term, so that variables can be avoided from bound variables.
	 */
	Term subst(std::string_view const& var, CTerm const& val) const;
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
		std::function<Term(std::string_view const&)> const& f,
		std::function<bool(std::string_view const&)> const&
			fixed = [](std::string_view const&){ return false; }
	) const {
		return _Mapper{f,fixed}.map(*this);
	};
	/** @brief instantiates the bound variable. This must be an abstraction.
	 * 
	 * @param arg should be a closed term, for efficiency
	 * @return Term 
	 */
	Term inst(CTerm const& arg) const;
private:
	void _iter_syms(
		StrMSet& bsyms,
		std::function<void(std::string_view const&)> const& bsym,
		std::function<void(std::string_view const&)> const& fsym
	) const;
	/** equality test */
	static bool _eq(Term const& l, Term const& r, StrMap<unsigned int>& lmap, StrMap<unsigned int>& rmap, unsigned int depth);

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
	return Term(IMP)(l)(r);
}
/** for all */
inline Term operator&=(std::string_view const& v, Term const& s) {
	return Term(ALL)(v/=s);
}

struct Error : public std::exception {
	Term term;
	Error(Term const& term) : term(term) {}
	Error operator()(Term const& arg) const {
		return term(arg);
	}
};
struct UnexpectedTerm : public Error {
	UnexpectedTerm(Term const& term) : Error(Term("#unexpected_term")(term)) {}
};
struct MalformedObtain : public Error {
	MalformedObtain(Term const& term) : Error(Term("#malformed-obtain")(term)) {}
};
struct MalformedInstantiation : public Error {
	MalformedInstantiation(Term const& all, Term const& arg) :
		Error(Term("#malformed_instantiation")(all)(arg)) {}
};
inline Error const MalformedDischarge = Error("#malformed_discharge");

inline Error const MalformedRetain = Error("#malformed-retain");

struct MissingProof : public Error {
	MissingProof(Term const& term) : Error(Term("#missing_proof")(term)) {}
};
struct WrongContext : public Error {
	WrongContext(std::string_view const& msg) : Error(Term("#wrong_context")(msg)) {}
};

struct DoubleFix : public Error {
	DoubleFix(std::string_view const& name) : Error(Term("#double_fix")(name)) {}
};

struct UnboundVariable : public Error {
	UnboundVariable(std::string_view const& name) : Error(Term("#unbound_variable")(name)) {}
};

struct ConstantEscape : public Error {
	ConstantEscape(std::string_view const& name) : Error(Term("#escape")(name)) {}
};

/** @brief Context */
class Ctxt {
private:
	struct Body;
	Ref<Body> _ref;
	Ctxt(Ref<Body>&& ref) : _ref(ref) {}
	class _Fix : public std::string {
		using std::string::string;
	};
	class _Assume : public Term {};
	struct _Obtain {
		std::string sym;
		Term thm;// ∀thesis. (∀sym. prop... ⟹ thesis) ⟹ thesis
		Term spec;// sym. ∀thesis. (prop... ⟹ thesis) ⟹ thesis
	};
	using _Modifier = Sum<_Fix,_Assume,_Obtain>;
public:
	Ctxt(Ctxt const& other) : _ref(other._ref) {}
	Ctxt(Ctxt&& other) : _ref(std::move(other._ref)) {}
	/** The root Ctxt */
	Ctxt();
	/** unique ID of the context */
	void const* id() const &;
	/** Optionally returns the parent context. */
	Opt<Ctxt const&> find_parent() const &;
	/** @brief Obtains the parent context.
	 * @exception WrongContext is thrown if no such context is found.
	 */
	Ctxt const& parent() const & {
		auto opt = find_parent();
		if( !opt ) {
			throw WrongContext("parent of root context");
		}
		return *opt;
	}
	/** @brief Tests if this has the given context as an ancestor.
	 */
	bool has_ancestor(Ctxt const& ancestor) const {
		Ctxt cur = *this;
		for(;;) {
			if( cur == ancestor ) {
				return true;
			}
			if( auto const& parent = cur.find_parent() ) {
				cur = *parent;
			} else {
				return false;
			}
		}
	}
	/** The set of locally fixed variables. */
	StrSet const& fvars() const&;
	/** The variable fixed at i-th modification. */
	Opt<std::string const&> fixed(size_t i) const&;
	/** The assumption made at the i-th modification. */
	Opt<Thm> assumed(size_t i) const&;
	/** The constant name obtained at the i-th modification. */
	Opt<std::tuple<std::string,Thm,Thm>> obtained(size_t i) const&;
	/** Revision of the context, i.e., how many modifications are made. */
	size_t revision() const;
	/** Tests if a variable is locally fixed. */
	Opt<CTerm> fixes(std::string_view const& name) const;
	/** Locally obtained constants. */
	StrSet const& consts() const&;
	/** Tests if a variable is locally obtained. */
	Opt<CTerm> obtains(std::string_view const& name) const;
	/** tests if a symbol is fixed in this or ancestor contexts. */
	bool has_constant(std::string_view const& sym) const;
	/** tests if a symbol is fixed in this or ancestor contexts. */
	Opt<CTerm> constant(std::string_view const& sym) const;
	/** Tests if a term is closed in this context. */
	Opt<CTerm> closed(Term const& t) const;
	/** Ensures that a term is closed in this context. */
	CTerm cterm(Term const& t) const;
	/** Make the term closed by fixing free variables. */
	CTerm enclose(Term const& t);
	/** @brief Fixes a local variable.
	 * 
	 * @param name 
	 * @return the closed term for the variable.
	 */
	CTerm fix(std::string_view const& name);
	/** @brief Adds an assumption.
	 * 
	 * @param t the assumption, which should be closed in the context.
	 * @return the assumed theorem.
	 */
	Thm assume(CTerm const& t);
	/** @brief Adds an assumption. Free variables will be fixed.
	 * 
	 * @param t the assumption.
	 * @return the assumed theorem.
	 */
	Thm assume(Term const& t);
	/** @brief Fixes a symbol with a specification.
	 *
	 * @param thm of form ∀thesis. (∀sym. props... ⟹ thesis) ⟹ thesis
	 * @return the fixed sym and theorem stating ∀thesis. (props... ⟹ thesis) ⟹ thesis
	 */
	std::pair<CTerm,Thm> obtain(std::string_view const& sym, Thm const& thm);
	
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
	/** Parent context. */
	Opt<Ctxt> const ctxt;
	/** Vector of modifiers */
	std::vector<_Modifier> modifiers;
	/** The set of locally fixed variables (excluding ancestors). */
	StrSet fvars;
	/** Locally obtained constants and their specifications. */
	StrSet constants;
};
inline void const* Ctxt::id() const & {
	return (void*)&*_ref;
}
/** @brief dummy: Contexts are equal only if they have the same reference to the body.
 * Therefore, two context bodies are always considered unequal.
 */
inline bool operator==(Ctxt::Body const& l, Ctxt::Body const& r) {
	return false;
};

inline Opt<Ctxt const&> Ctxt::find_parent() const & {
	if( _ref->ctxt ) {
		return *_ref->ctxt;
	}
	return {};
}
inline size_t Ctxt::revision() const {
	return _ref->modifiers.size();
}
inline Opt<std::string const&> Ctxt::fixed(size_t i) const & {
	if( i < revision() ) {
		if( auto a = _ref->modifiers[i].ref<_Fix>() ) {
			return *a;
		}
	}
	return {};
}

inline StrSet const& Ctxt::fvars() const& {
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
	/** @brief Decompose closed fix
	 * returns tuple of string, closed term of the variable, and the argument
	 */
	Opt<std::tuple<std::string const, CTerm const, CTerm const>> cfix() const {
		if( auto tfix = Term::fix() ) {
			auto [v,b] = *tfix;
			return std::tuple(v,CTerm(_ctxt,v),CTerm(_ctxt,b));
		}
		return {};
	}
	/** @brief Decompose closed binders
	 * 
	 * @param b the binder
	 * @return If this is binding, the pair of the bound variable and the body, belonging to a new context that fixes the bound variable.
	 */
	Opt<StrTerm> cbinder( std::string_view const& b ) const {
		if( auto app = capp() ) {
			if( app->first == b ) {
				return app->second.cabs();
			}
		}
		return {};
	}
	/** @brief Decompose closed unary function.
	 * 
	 * @param f expected function
	 * @return the argument, if matches
	 */
	Opt<CTerm const> cunary( std::string_view const& f ) const {
		if( auto un = unary(f) ) {
			return CTerm(_ctxt,*un);
		}
		return {};
	}
	/** @brief Decompose closed binary operation
	 * 
	 * @param f the binary function
	 * @return If this is application of f, then the pair of arguments.
	 */
	Opt<Pair> cbinary( std::string_view const& f ) const {
		if( auto bin = binary(f) ) {
			auto [s,t] = *bin;
			return Pair(CTerm(_ctxt,s),CTerm(_ctxt,t));
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
		return CTerm(_ctxt,Term::inst(arg));
	}
	/** @brief Moves a closed term to a descendant context
	 * 
	 * @param ctxt the descendant context
	 * @return CTerm 
	 */
	CTerm weaken(Ctxt const& ctxt) const {
		if( !ctxt.has_ancestor(_ctxt) ) {
			throw WrongContext("weaken");
		}
		return CTerm(ctxt,*this);
	}
	/** @brief Lifts a closed term to one with respect to the parent context.
	 *   Symbols fixed in the context will be quantified.
	 * @return the closed term with respect to the parent.
	 */
	CTerm lift(CTerm const& quantifier) const;
	/** @brief Moves the statement to the parent context.
	 * Context-bound symbols will be universally quantified,
	 * and assumptions are made into implication.
	 */
	CTerm intro() const;
	friend Term;
	friend Thm;
	friend Ctxt;
	friend Intp;
	friend CSubst;
	friend bool operator==(CTerm const& l, CTerm const& r) {
		return l._ctxt == r._ctxt && (Term)l == (Term)r;
	}
	/** closed implication */
	friend CTerm operator>>=(CTerm const& l, CTerm const& r) {
		if( l._ctxt != r.ctxt() ) {
			throw WrongContext("⟹");
		}
		return CTerm( l._ctxt, (Term)l >>= r );
	}
	/** closed abstraction */
	friend CTerm operator/=(std::string_view const& v, CTerm const& body ) {
		return CTerm( body._ctxt, v /= (Term)body );
	}
	/** closed binding */
	friend CTerm operator/(std::string_view const& v, CTerm const& arg) {
		if( !arg._ctxt.constant(v) ) {
			throw UnboundVariable(v);
		}
		return CTerm( arg._ctxt, v %= (Term)arg );
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
	/** @brief Creates a closed substituion
	 * @param ctxt the context the substitution is closed in
	 */
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
	bool contains(std::string_view const& var) const {
		return _map.contains(var);
	}
	/** @brief Tests if a variable is substituted or fixed in the context. */
	bool closes(std::string const& var) const {
		return contains(var) || _ctxt.constant(var);
	}
	void erase(std::string_view const& var) {
		_map.erase(var);
	}
	bool empty() const {
		return _map.empty();
	}
	/** @brief (re)assigns a value to a variable */
	CSubst& assign(std::string_view const& var, CTerm const& val) {
		if( val.ctxt() != _ctxt ) {
			throw WrongContext("CSubst::assign");
		}
		return _assign(var,val);
	}
	CSubst& assign(std::string_view const& var, Term const& val) {
		return _assign(var,_ctxt.cterm(val));// val should be closed wrt ctxt
	}
	Opt<CTerm> get(std::string_view const& var) const {
		if( auto it = _map.find(var); it != _map.end() ) {
			return CTerm(_ctxt,it->second);
		}
		return {};
	}
private:
	CSubst& _assign(std::string_view const& var, Term const& val);
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
	Thm intro() const {
		return CTerm::intro();
	}
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
};
/** @brief Interpreter, translates facts of a context into the context it belongs. */
class Intp {
	/** @brief Instantiation of the symbols of the source context, closed in the target context. */
	CSubst _subst;
	Ctxt _src;// the source context
	int _rev;// supported revision of the source
public:
	/** @brief makes initial interpretation.
	 @param src the context to be interpreted
	 @param tgt the context that interprets src
	 */
	Intp(Ctxt const& src, Ctxt const& tgt);
	Ctxt ctxt() {
		return _subst.ctxt();
	};
	size_t revision() const {
		return _rev;
	}
	/** tests if there is no pending modification */
	bool ready() const {
		return _rev == _src.revision();
	}
	/** @brief next unprocessed fix. */
	Opt<std::string const&> fixing() const & {
		return _src.fixed(_rev);
	}
	Opt<CTerm> assuming() const {
		if( auto a = _src.assumed(_rev) ) {
			return a->csubst(_subst);
		}
		return {};
	}
	Opt<std::tuple<std::string,Thm,Thm>> obtaining() const {
		if( auto o = _src.obtained(_rev) ) {
			auto const& [sym,ex,spec] = *o;
			return {{sym,Thm(ex.csubst(_subst)),Thm(spec.csubst(_subst))}};
		}
		return {};
	}
	/** @brief instantiates a closed term. */
	CTerm subst(CTerm const& t) const;
	/** @brief instantiates a theorem. */
	Thm subst(Thm const& thm) const {
		return subst((CTerm)thm);
	}
	/** @brief Instantiates a context variable.
	 * If the interpreted context is modified by fixing a new variable,
	 * then this method should be used to instantiate the variable.
	 * @param term 
	 */
	void instantiate(CTerm const& term);
	/** @brief Interprets an assumption.
	 * If the interpreted context is modified by an assumption,
	 * this method should be used to discharge the instantiated assumption.
	 * @param thm Proof of the instantiated assumption.
	 */
	void discharge(Thm const& thm);
	/** @brief If the interpreted context is modified by obtaining a constant,
	 * then this method should be used to instantiate the constant.
	 * @param term that should play the role of the constant.
	 * @param spec of form ∀thesis. (props[sym:=term]... ⟹ thesis) ⟹ thesis,
	 * where the obtained constant is replaced by the term.
	 */
	void retain(CTerm const& term, Thm const& spec);
	friend Ctxt;
};

inline Opt<CTerm> Ctxt::fixes(std::string_view const& name) const {
	if( auto it = fvars().find(name); it != fvars().end() ) {
		return CTerm(*this,*it);
	}
	return {};
}
inline Opt<CTerm> Ctxt::obtains(std::string_view const& name) const {
	if( auto it = consts().find(name); it != consts().end() ) {
		return CTerm(*this,*it);
	}
	return {};
}
inline Opt<CTerm> Ctxt::constant(std::string_view const& sym) const {
	if( has_constant(sym) ) {
		return CTerm(*this,sym);
	}
	return {};
}
inline Opt<Thm> Ctxt::assumed(size_t i) const & {
	if( i < revision() ) {
		if( auto a = _ref->modifiers[i].ref<_Assume>() ) {
			return Thm(CTerm(*this,*a));
		}
	}
	return {};
}
inline Opt<std::tuple<std::string,Thm,Thm>> Ctxt::obtained(size_t i) const & {
	if( i < revision() ) {
		if( auto o = _ref->modifiers[i].ref<_Obtain>() ) {
			auto const& [sym,thm,spec] = *o;
			return {{sym,CTerm(*this,thm),CTerm(*this,spec)}};
		}
	}
	return {};
}

// workaround for Visual Studio...?
//template<> inline constexpr bool std::is_nothrow_constructible_v<Ctxt,Ctxt&> = true;

#endif
