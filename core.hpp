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
#define DEBval(expr) [&]{ auto ret = (expr); DEB(ret); return ret; }()

class Term;
class Error;
class Ctxt;
class Thm;
class CTerm;
class Subst;
class Intp;

/** @brief renames a variable so that it is not in the set of symbols.
 * 
 * @param var variable to be made fresh
 * @param test avoided names
 */
std::string avoid(std::string_view const& var, std::function<bool(std::string_view const&)> const& test);

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
	struct Unbind : Ref<StrTerm const> {
		Unbind(std::string_view const& var, Term const& val) : Ref(Ref<StrTerm const>::make(var,val)) {}
	};
	Sum<std::string,App,Abs,Unbind> _un;
	struct _Mapper {
		std::function<Opt<Term>(std::string const&)> const& f;
		std::function<bool(std::string_view const&)> const& avoided;
		StrMap<std::string> bsyms;
		std::string rename( std::string_view const& var ) const {
			return avoid(var,[&](std::string_view const& x){ return bsyms.contains(x) || avoided(x); });
		}
		Opt<Term> map_var( std::string const& sym ) {
			if( auto opt = bsyms.finds(sym) ) {
				return opt->second;
			}
			return f(sym);
		}
		Opt<Term> map( Term const& t );
	};
	Term(App const& app) : _un(app) {}
	Term(Abs const& abs) : _un(abs) {}
	Term(Unbind const& bind) : _un(bind) {}
public:
	Term() {}
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
	/** @brief binding */
	friend Term operator/=(std::string_view const& var, Term const& body) {
		return Term(Abs{var,body});
	}
	/** @brief unbinding
	 * 
	 * @param binder 
	 * @param val 
	 * @return Term 
	 */
	friend Term operator%=(std::string_view const& binder, Term const& val) {
		return Term(Unbind{binder,val});
	}
	/** @brief Move the string if the temporary term is a symbol. */
	Opt<std::string> sym() && {
		return std::move(_un).ref<std::string>();
	}
	/** @brief Reference to the string if the term a symbol. */
	Opt<std::string const&> sym() const & {
		return _un.ref<std::string>();
	}
	/** @brief Move the function and argument if the term is an application. */
	Opt<Pair> app() && {
		if( auto const& opt = std::move(_un).ref<App>() ) {
			return {**opt};
		}
		return {};
	}
	/** @brief Reference to the function and argument if the term is an application. */
	Opt<Pair const&> app() const & {
		if( auto opt = _un.ref<App>() ) {
			return {**opt};
		}
		return {};
	}
	/** @brief Move of the variable and body if the term is an abstraction. */
	Opt<StrTerm> bind() && {
		if( auto const& opt = std::move(_un).ref<Abs>() ) {
			return {**opt};
		}
		return {};
	}
	/** @brief Reference to the variable and body if the term is an abstraction. */
	Opt<StrTerm const &> bind() const & {
		if( auto opt = _un.ref<Abs>() ) {
			return {**opt};
		}
		return {};
	}
	/** @brief Move the variable and body if the term is a binding. */
	Opt<StrTerm> unbind() && {
		if( auto const& opt = std::move(_un).ref<Unbind>() ) {
			return {**opt};
		}
		return {};
	}
	/** @brief Reference to the variable and body if the term is a binding. */
	Opt<StrTerm const &> unbind() const & {
		if( auto opt = _un.ref<Unbind>() ) {
			return {**opt};
		}
		return {};
	}
	/** @brief Decompose binders.
	 * @param b expected binder (quantifier)
	 */
	Opt<StrTerm const&> binder( std::string_view const& b ) const & {
		if( auto opt1 = app() )
		if( opt1->first == b ) {
			return opt1->second.bind();
		}
		return {};
	}
	/** @brief Decompose binders.
	 * @param b expected binder (quantifier)
	 */
	Opt<StrTerm> binder( std::string_view const& b ) && {
		if( auto opt = binder(b) ) {
			return {std::move(*opt)};
		}
		return {};
	}
	/** @brief Decompose unary function.
	 * 
	 * @param f expected function
	 * @return the argument, if matches
	 */
	Opt<Term const&> unary( std::string_view const& f ) const & {
		if( auto opt = app() )
		if( opt->first == f ) {
			return {opt->second};
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
			return {std::move(*opt)};
		}
		return {};
	}
	/** @brief Decompose binary function application
	 * 
	 * @param f expected function symbol
	 * @return the pair of arguments, in case of match
	 */
	Opt<std::pair<Term const&,Term const&>> binary( std::string_view const& f ) const & {
		if( auto x = app() )
		if( auto a = x->first.unary(f) ) {
			return {{*a,x->second}};
		}
		return {};
	}
	/** @brief Decompose binary function application
	 * 
	 * @param f expected function symbol
	 * @return the pair of arguments, in case of match
	 */
	Opt<Pair> binary( std::string_view const& f ) && {
		if( auto x = binary(f) ) {
			return {{std::move(x->first),std::move(x->second)}};
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
	/** @brief Singleton substitution
	 * @param val it must be closed term, so that variables can be avoided from bound variables.
	 */
	Term subst(std::string_view const& var, CTerm const& val) const;
	/** @brief applies a substitution.
	 * 
	 * @param subst
	 * @return result of substitution
	 */
	Term subst(Subst const& subst) const;
	/** @brief Applies a closed substitution and get a closed term.
	 * 
	 * @param subst a substitution closed in a context.
	 * @return the instance, closed in the same context.
	 */
	CTerm csubst(Subst const& subst) const;
	/** @brief homomorphic extension.
	 * 
	 * @param f the mapping applied on free variables.
	 * @param avoided flags symbols to be avoided.
	 * @return Term 
	 */
	Term map(
		std::function<Opt<Term>(std::string_view const&)> const& f,
		std::function<bool(std::string_view const&)> const&
			avoided = [](std::string_view const&){ return false; }
	) const {
		return _Mapper{f,avoided}.map(*this).ref(*this);
	};
	/** @brief instantiates the bound variable. This must be a binding.
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
	bool operator==( std::string const& y ) {
		if( auto const& x = sym() ) {
			return *x == y;
		};
		return false;
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

struct Error : public std::exception, Term {
	Error(Term const& term) : Term(term) {}
	Error operator()(Term const& arg) const {
		return Term::operator()(arg);
	}
};
struct UnboundVariable : public Term {
	UnboundVariable( std::string_view const& name ) : Term(Term("#ctxt")("\"unbound variable\"")(name)) {}
};
/** @brief Context */
class Ctxt {
private:
	struct Body;
	Ref<Body> _ref;
	Ctxt(Ref<Body>&& ref) : _ref(ref) {}
	Ctxt(Opt<Ctxt> const& parent);
	Thm _assume(Term const& t) &;
public:
	struct Fix : public std::string {};
	class Assume : public Term {};
	struct Obtain {
		std::string sym;
		Term ex;// ∀thesis. (∀sym. prop... ⟹ thesis) ⟹ thesis
		Term spec;// sym. ∀thesis. (prop... ⟹ thesis) ⟹ thesis
	};
	Ctxt(Ctxt const& other) : _ref(other._ref) {}
	Ctxt(Ctxt&& other) : _ref(std::move(other._ref)) {}
	/** The root Ctxt */
	Ctxt();
	/** unique ID of the context */
	void const* id() const &;
	/** @brief Optionally returns the parent information.
	 * @return the pair of the parent context and the revision when this context was forked.
	 */
	Opt<std::pair<Ctxt,size_t> const&> find_parent() const &;
	/** @brief Obtains the parent information.
	 * @exception is thrown if no such context is found.
	 */
	std::pair<Ctxt,size_t> const& parent() const & {
		auto opt = find_parent();
		if( !opt ) throw Error(__func__)("\"parent of root\"");
		return *opt;
	}
	/** The variable fixed at i-th modification. */
	Opt<std::string const&> fixed(size_t i) const&;
	/** The assumption made at the i-th modification. */
	Opt<Thm> assumed(size_t i) const&;
	/** The constant name obtained at the i-th modification. */
	Opt<std::tuple<std::string,Thm,CTerm>> obtained(size_t i) const&;
	/** Revision of the context, i.e., how many modifications are made. */
	size_t revision() const;
	/** Tests if a variable is locally fixed. */
	bool fixes(std::string_view const& v ) const;
	/** Tests if a variable is locally obtained. */
	Opt<CTerm> obtains(std::string_view const& name) const;
	/** tests if a symbol is fixed in this or ancestor contexts. */
	bool has_constant(std::string_view const& sym) const;
	/** tests if a symbol is fixed in this or ancestor contexts. */
	Opt<CTerm> constant(std::string_view const& sym) const;
	/** Ensures that a term is closed in this context. */
	CTerm cterm(Term const& t) const;
	/** Tests if a term is closed in this context. */
	Opt<CTerm> closed(Term const& t) const;
	/** Tests if a closed term term is also closed in this context. */
	Opt<CTerm> closed(CTerm const& t) const;
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
	/** @brief Returns the self interpretation. */
	Intp self() const;
	/** @brief Creates a child context.
	 * @return interpretation of the parent in the child.
	 */
	Intp fork() const;
	Ctxt& operator=(Ctxt const& other)& = default;
	Ctxt& operator=(Ctxt && other)& = default;
	friend bool operator==(Ctxt const& l, Ctxt const& r) {
		return l._ref == r._ref;
	};
	friend CTerm;
	friend Intp;
};

struct Ctxt::Body {
	using _Modifier = Sum<Fix,Assume,Obtain>;
	/** Parent context and its revision. */
	Opt<std::pair<Ctxt,size_t>> parent;
	/** Vector of modifiers */
	std::vector<_Modifier> modifiers;
	/** The set of locally fixed variables (excluding ancestors). */
	StrSet fvars;
	/** Locally obtained constants and their specifications. */
	StrSet constants;
	/** @brief dummy: Contexts are equal only if they have the same reference to the body.
	 * Therefore, two context bodies are always considered unequal.
	 */
	inline bool operator==(Body const& r) {
		return false;
	};
};
inline void const* Ctxt::id() const & {
	return (void*)&*_ref;
}
inline Opt<std::pair<Ctxt,size_t> const&> Ctxt::find_parent() const & {
	return _ref->parent;
}
inline size_t Ctxt::revision() const {
	return _ref->modifiers.size();
}

inline Opt<std::string const&> Ctxt::fixed(size_t i) const & {
	if( i < revision() )
	if( auto a = _ref->modifiers[i].ref<Fix>() ) {
		return *a;
	}
	return {};
}

inline bool Ctxt::fixes( std::string_view const& v ) const {
	return _ref->fvars.contains(v);
};
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
	 * @return If this is an abstraction, the triple of the bound variable, interpretation into a child context that fixes the bound variable, and the body in the child.
	 */
	Opt<std::tuple<std::string,Intp,CTerm>> cbind() const;
	/** @brief Decompose closed fix
	 * returns tuple of string, closed term of the variable, and the argument
	 */
	Opt<std::tuple<std::string const, CTerm const, CTerm const>> cunbind() const {
		if( auto tfix = Term::unbind() ) {
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
	Opt<std::tuple<std::string,Intp,CTerm>> cbinder( std::string_view const& b ) const;
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
		if( _ctxt != arg._ctxt ) throw Error(__func__)("\"wrong context application\"");
		return CTerm(_ctxt,Term::operator()(arg));
	}
	/** @brief closed substitution */
	CTerm subst(Intp const& subst) const;
	/** @brief instantiates the bound variable. This must be an abstraction.
	 * 
	 * @param arg
	 * @return CTerm 
	 */
	CTerm inst(CTerm const& arg) const {
		if( arg._ctxt != _ctxt ) throw Error("#core")("\"wrong context inst\"");
		return CTerm(arg._ctxt,Term::inst(arg));
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
	friend Subst;
	friend bool operator==(CTerm const& l, CTerm const& r) {
		return l._ctxt == r._ctxt && (Term)l == (Term)r;
	}
	/** closed implication */
	friend CTerm operator>>=(CTerm const& l, CTerm const& r) {
		if( l._ctxt != r._ctxt ) throw Error(__func__)("\"wrong context implication\"");
		return CTerm( l._ctxt, (Term)l >>= r );
	}
	/** closed abstraction */
	friend CTerm operator/=(std::string_view const& v, CTerm const& body ) {
		return CTerm( body._ctxt, v /= (Term)body );
	}
	/** closed binding */
	friend CTerm operator/(std::string_view const& v, CTerm const& arg) {
		if( !arg._ctxt.constant(v) ) throw Error(__func__)("\"wrong context binding\"")(v);
		return CTerm( arg._ctxt, v %= (Term)arg );
	}
};
inline bool operator!=(CTerm const& l, CTerm const& r) {
	return !(l == r);
};
inline CTerm Ctxt::cterm(Term const& t) const {
	t.iter_syms( [&](auto sym){
		if( !has_constant(sym) ) throw UnboundVariable(sym);
	} );
	return CTerm(*this,t);
}
inline Opt<CTerm> Ctxt::closed(Term const& t) const try {
	return cterm(t);
} catch( UnboundVariable const& e ) {
	return {};
}
inline Opt<CTerm> Ctxt::closed(CTerm const& t) const {
	if( t.ctxt() == *this ) return {t};
	return closed((Term)t);
}
/** @brief Substitution.
 * For efficiency, the range should be closed with respect to a common context.
 */
class Subst {
	bool _identity;
	StrMap<Opt<Term>> _map;
	Ctxt _ctxt;
	Subst& _assign(std::string_view const& var, Term const& val) &;
public:
	/** @brief Creates an identity substituion
	 * @param ctxt the context the substitution is closed in
	 */
	Subst(Ctxt const& ctxt) : _ctxt(ctxt), _identity(true) {}
	/** @brief The context in which the range of the substitution is closed. */
	Ctxt const& ctxt() const& {
		return _ctxt;
	}
	Ctxt ctxt() && = delete;
	/** @brief The map from variable names to the substitutes.
	 * 
	 * @return StrMap<Term> const& 
	 */
	StrMap<Opt<Term>> const& map() const& {
		return _map;
	}
	auto map() && = delete;
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
	bool identity() const {
		return _identity;
	}
	/** @brief (re)assigns a value to a variable */
	Subst& assign(std::string_view const& var, CTerm const& val) & {
		if( val.ctxt() != _ctxt ) throw Error(__func__)("\"wrong context assign\"");
		return _assign(var,val);
	}
	Subst& assign(std::string_view const& var, Term const& val) & {
		return _assign(var,_ctxt.cterm(val));// val should be closed wrt ctxt
	}
	Opt<CTerm> get(std::string_view const& var) const {
		if( auto it = _map.find(var); it != _map.end() ) {
			return CTerm( _ctxt, it->second ? *it->second : var );
		}
		return {};
	}
	friend Term;
	friend Intp;
};

class Thm : public CTerm {
	/** @brief Trusted construction of Thm. This being private is crucial. */
	Thm(CTerm const& t) : CTerm(t) {}
	Thm() = delete;
public:
	Thm( Thm const& t ) = default;
	Thm& operator=(Thm const& other) & {
		CTerm::operator=(other);
		return *this;
	}
	/** @brief forall elimination. This theorem must be of form ∀x. P(x).
	 * @return Thm P(t)
	 * @exception _MalformedInst
	 */
	Thm instantiate(Term const& t) const {
		return _instantiate(_ctxt.cterm(t));
	}
	Thm instantiate(CTerm const& t) const {
		if( t._ctxt != _ctxt ) throw Error(__func__)("\"wrong context instantiate\"");
		return _instantiate(t);
	}
	/** @brief implication elimination.
	 * 
	 * @param t the premise.
	 * @return The conclusion if this theorem is an implication whose premise is t. None otherwise.
	 * @exception MalformedDischarge
	 * @exception WrongContext
	 */
	Opt<Thm> discharges(Thm const& t) const;
	Thm discharge(Thm const& t) const {
		auto o = discharges(t);
		if( !o ) throw Error(__func__)("\"malformed discharge\"")(*this)(t);
		return *o;
	}
	/** @brief Moves the theorem to the parent context.
	 * Context-bound symbols will be universally quantified,
	 * and assumptions are made into implication.
	 */
	Thm intro() const {
		return CTerm::intro();
	}
	Thm subst(Intp const& intp) const;
private:
	Thm _instantiate(CTerm const& t) const {
		auto const& a = cunary(ALL);
		if(!a) throw Error(__func__)("\"malformed instantiate\"")(*this)(t);
		return a->inst(t);
	}
	friend Ctxt;
	friend Intp;
};
inline Thm Ctxt::_assume(Term const& t) & {
	_ref->modifiers.push_back(Assume(t));
	return CTerm(*this,t);
}
inline Thm Ctxt::assume(CTerm const& t) {
	if( t.ctxt() != *this ) throw Error(__func__)("wrong context assume");
	return _assume(t);
}
inline Thm Ctxt::assume(Term const& t) {
	return _assume(enclose(t));
}

/** @brief Interpreter, translates facts of a context into the context it belongs. */
class Intp {
	/** @brief Instantiation of the symbols of the source context, closed in the target context. */
	Subst _subst;
	Ctxt _src;// the source context
	int _rev;// supported revision of the source
	/** @brief makes initial interpretation.
	 @param src the context to be interpreted
	 @param tgt the context that interprets src
	 */
	 explicit Intp(Ctxt const& src, Subst const& tgt, int rev) : _subst(tgt), _src(src), _rev(rev) {}
public:
	/** @brief makes a direct interpretation. */
	static Intp make( Ctxt const& src, Ctxt const& tgt );
	Ctxt source() && {
		return std::move(_src);
	}
	Ctxt const& source() const & {
		return _src;
	}
	Ctxt ctxt() const& {
		return _subst.ctxt();
	}
	operator Subst const&() const& {
		return _subst;
	}
	operator Subst const&() && = delete;
	Subst const& subst() const& {
		return _subst;
	}
	auto subst() && = delete;
	size_t revision() const {
		return _rev < 0 ? _src.revision() : _rev;
	}
	/** tests if there is no pending modification */
	bool ready() const {
		return _rev < 0 /* indicates trivial interpretation */ || _rev == _src.revision();
	}
	/** @brief tests if the substitution is identity */
	bool identity() const {
		return _subst.identity();
	}
	/** unprocessed modification */
	Sum<Ctxt::Fix,Ctxt::Assume,Ctxt::Obtain,nullptr_t> modification( size_t i ) const& {
		if( _rev < 0 ) {
			return nullptr;
		}
		auto ind = _rev + i;
		if( _src.revision() <= ind ) {
			return nullptr;
		}
		auto const& m = _src._ref->modifiers[ind];
		if( auto const& sym = m.ref<Ctxt::Fix>() ) {
			return Ctxt::Fix(*sym);
		}
		if( auto const& assm = m.ref<Ctxt::Assume>() ) {
			return Ctxt::Assume{assm->subst(_subst)};
		}
		if( auto const& obtain = m.ref<Ctxt::Obtain>() ) {
			auto const& [sym,ex,spec] = *obtain;
			return Ctxt::Obtain{sym,ex.subst(_subst),spec.subst(_subst)};
		}
		assert(false);
	}
	/** @brief returns the next fixed symbol */
	Opt<std::string const&> fixing() const {
		if( 0 <= _rev && _rev < _src.revision() )
		if( auto const& fix = _src._ref->modifiers[_rev].ref<Ctxt::Fix>() ) {
			return {*fix};
		}
		return {};
	}
	/** @brief returns the next assumption */
	Opt<CTerm> assuming() const {
		if( 0 <= _rev && _rev < _src.revision() )
		if( auto const& assume = _src._ref->modifiers[_rev].ref<Ctxt::Assume>() ) {
			return {CTerm(_subst.ctxt(),assume->subst(_subst))};
		}
		return {};
	}
	/** returns the next obtained symbol.
	 * @return tuple of
	 *  - the symbol x
	 *  - the existence theorem: ∀thesis. (∀x. Pθ[x] ⟹ thesis) ⟹ thesis
	 *  - and the specification: x. Pθ[x]
	 */
	Opt<std::tuple<std::string,Thm,CTerm>> obtaining() const {
		if( 0 <= _rev && _rev < _src.revision() )
		if( auto const& obtain = _src._ref->modifiers[_rev].ref<Ctxt::Obtain>() ) {
			return {{obtain->sym,Thm(CTerm(_subst.ctxt(),obtain->ex.subst(_subst))),CTerm(_subst.ctxt(),obtain->spec.subst(_subst))}};
			}
		return {};
	}
	/** @brief Instantiates a context variable.
	 * If the interpreted context is modified by fixing a new variable,
	 * then this method should be used to instantiate the variable.
	 * @param term 
	 */
	void instantiate(CTerm const& term) {
		auto fix = fixing();
		if( !fix ) throw Error(__func__)("\"unexpected\"");
		_subst.assign(*fix,term);
		_rev++;
	}
	/** @brief Interprets an assumption.
	 * If the interpreted context is modified by an assumption,
	 * this method should be used to discharge the instantiated assumption.
	 * @param thm Proof of the instantiated assumption.
	 */
	void discharge(Thm const& thm) {
		auto assm = assuming();
		if( !assm ) throw Error(__func__)("\"unexpected\"");
		if( assm->ctxt() != thm.ctxt() ) throw Error("\"context mismatch\"");
		if( (Term)*assm != thm ) throw Error(__func__)("\"malformed\"")(*assm)(thm);
		_rev++;
	}
	/** @brief If the interpreted context is modified by obtaining a constant,
	 * then this method should be used to instantiate the constant.
	 * @param term that should play the role of the constant.
	 * @param thm of form ∀thesis. (props[sym:=term]... ⟹ thesis) ⟹ thesis,
	 * where the obtained constant is replaced by the term.
	 */
	void retain(CTerm const& term, Thm const& thm) {
		if( thm.ctxt() != _subst.ctxt() ) throw Error(__func__)("\"wrong context retain\"");
		auto obtain = obtaining();
		if( !obtain ) throw Error(__func__)("\"unexpected retain\"");
		auto const& [sym,ex,spec] = *obtain;
		if( spec.inst(term) != thm ) throw Error(__func__)("\"malformed retain\"")(thm);
		_subst.assign(sym,term);
		_rev++;
	}
	/** @brief composes with other interpretation.
	 * The other interpretation should readily intepret the context this interpretation belongs.
	 * @param other interpretation to be composed with.
	 * @return an interpretation of this source in the other context.
	 */
	Intp compose(Intp const& other) const;
	friend Ctxt;
	friend CTerm;
	friend Thm;
};
inline Intp Ctxt::self() const {
	return Intp(*this,*this,-1);
}
inline Intp Ctxt::fork() const {
	auto child = Ctxt(Ref<Body>::make());
	auto rev = revision();
	child._ref->parent = {{*this,rev}};
	return Intp(*this,child,rev);
}
inline Opt<CTerm> Ctxt::obtains(std::string_view const& name) const {
	if( auto it = _ref->constants.find(name); it != _ref->constants.end() ) {
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
	if( i < revision() )
	if( auto a = _ref->modifiers[i].ref<Assume>() ) {
		return Thm(CTerm(*this,*a));
	}
	return {};
}
inline Opt<std::tuple<std::string,Thm,CTerm>> Ctxt::obtained(size_t i) const & {
	if( i < revision() )
	if( auto o = _ref->modifiers[i].ref<Obtain>() ) {
		auto const& [sym,thm,spec] = *o;
		return {{sym,CTerm(*this,thm),CTerm(*this,spec)}};
	}
	return {};
}

inline CTerm CTerm::subst(Intp const& intp) const {
	if( _ctxt != intp._src ) throw Error(__func__)("\"wrong context subst\"")(*this);
	if( !intp.ready() ) throw Error(__func__)("\"interpretation not ready\"")(*this);
	return CTerm(intp.ctxt(),this->Term::subst(intp));
}

inline Thm Thm::subst(Intp const& intp) const {
	return CTerm::subst(intp);
}

// workaround for Visual Studio...?
//template<> inline constexpr bool std::is_nothrow_constructible_v<Ctxt,Ctxt&> = true;

#endif
