#include<cassert>
#include<map>
#include<cstring>
#include<string>
#include<vector>
#include<set>
#include<iostream>
#include <exception>

using namespace std;

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

class Ctxt;

class Term {
	struct App;
	struct Abs;
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
	typedef enum { SYM, APP, ABS } Type;
private:
	Type _type;
	union Union {
		char const* sym;
		Ref<App const> app;
		Ref<Abs const> abs;
		Union() {}
		~Union() {}
		Union(char const* sym) : sym(sym) {}
		Union(Ref<App const> const& app) : app(app) {}
		Union(Ref<Abs const> const& abs) : abs(abs) {}
	} _un;
	Term() = delete; // uninitialized constructor is not allowed
	Term* operator&() { // making pointer is private
		return this;
	}
	Term(Term const& fun, Term const& arg); // application
	Term(char const* var, Term const& body); // abstraction
	Union _copy_un() const;
	bool _eq(Term const& r, VarMaker vars) const;// equality test
	/**
	 * @brief computes bound and free symbols.
	 * 
	 * @param bsyms bound symbols
	 * @param fsyms free symbols
	 */
	void _syms(set<string>& bsyms, set<string>& fsyms) const; // symbol set
public:
	Term(char const* sym) : _type(SYM), _un(sym) {} // symbol
	Term(Term const& other) : _type(other._type), _un(other._copy_un()) {}
	~Term();
	Type type() const {
		return _type;
	}
	Term& operator=(Term const& other) {
		Term temp1 = other;// copy other
		char temp2[sizeof *this];
		memcpy(temp2,this,sizeof *this);// remember old this
		memcpy(this,&temp1,sizeof *this);// new this is the copy
		memcpy(&temp1,temp2,sizeof *this);// temp1 is old this, to be destructed
		return *this;
	}
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
	char const* sym() const {
		assert( _type == SYM );
		return _un.sym;
	}
	Term const& fun() const;
	Term const& arg() const;
	char const* var() const;
	Term const& body() const;
	/**
	 * @brief The set of free symbols.
	 */
	set<string> syms() const;
	Term subst(char const* var, Term const& val) const;
	friend bool operator==(Term const& l, Term const& r) {
		return l._eq(r,VarMaker());
	}
};
bool operator!=(Term const& l, Term const& r) {
	return !(l == r);
}

vector<char const*> Term::VarMaker::vec;

struct Term::App {
	Term const fun;
	Term const arg;
};

struct Term::Abs {
	char const* const var;
	Term const body;
};

Term::Term(Term const& fun, Term const& arg) : _type(APP), _un(App{fun,arg}) {}

Term::Term(char const* var, Term const& body) : _type(ABS), _un(Abs{var,body}) {};

Term::Union Term::_copy_un() const {
	switch(_type) {
		case SYM: return Union(_un.sym);
		case APP: return Union(_un.app);
		case ABS: return Union(_un.abs);
	}
}

Term::~Term() {
	switch(_type) {
	case APP: _un.app.~Ref(); break;
	case ABS: _un.abs.~Ref(); break;
	case SYM: break;
	}
}

Term const& Term::fun() const {
	assert( _type == APP );
	return _un.app->fun;
}
Term const& Term::arg() const {
	assert( _type == APP );
	return _un.app->arg;
}
char const* Term::var() const {
	assert( _type == ABS );
	return _un.abs->var;
}
Term const& Term::body() const {
	assert( _type == ABS );
	return _un.abs->body;
}

bool Term::_eq(Term const& other, VarMaker vars) const {
	if( _type != other._type ) {
		return false;
	}
	switch(_type) {
		case SYM:
			return strcmp(sym(),other.sym()) == 0;
		case APP:
			return fun()._eq(other.fun(),vars) && arg()._eq(other.arg(),vars);
		case ABS: {
			// replace the bound variables with fresh one and compare
			Term fresh = Term(vars.make());
			Term l = body().subst(var(),fresh);
			Term r = other.body().subst(other.var(),fresh);
			return l._eq(r,vars);
		}
	}
}
void Term::_syms(set<string>& bsyms, set<string>& fsyms) const {
	switch(_type) {
		case SYM:
			if( bsyms.find(sym()) == bsyms.end() ) {
				fsyms.insert(sym());
			}
			return;
		case APP:
			fun()._syms(bsyms,fsyms);
			arg()._syms(bsyms,fsyms);
			return;
		case ABS:
			bsyms.insert(var());
			body()._syms(bsyms,fsyms);
			return;
	}
}
set<string> Term::syms() const {
	set<string> bsyms, fsyms;
	_syms(bsyms,fsyms);
	return fsyms;
}

Term Term::subst(char const* x, Term const& v) const {
	switch(_type) {
		case SYM:
			return strcmp(x,sym()) == 0 ? v : *this;
		case APP:
			return fun().subst(x,v)(arg().subst(x,v));
		case ABS:
			return strcmp(x,var()) == 0 ? *this : var() /= body().subst(x,v);
	}
}

ostream& operator<<(ostream& os, Term const& t) {
	switch(t.type()) {
	case Term::SYM:
		return os << t.sym();
	case Term::APP:
		return os << '(' << t.fun() << ' ' << t.arg() << ')';
	case Term::ABS:
		return os << t.var() << ". " << t.body();
	}
};

class MalformedInstantiation : public exception {};
class MalformedDischarge : public exception {};
class TheoremNotFound : public exception {};
class WrongContext : public exception {};
class InvalidForAll : public exception {};

class Thm;

class Ctxt {
private:
	set<string> _syms;
	vector<string> _sym_list;
	vector<Term> _assms;
	map<string, Term const> _thms; // table of theorems
	Ctxt() : name("root"), parent(NULL) {};// for building the root context
	Ctxt(char const* name, Ctxt const* parent) : name(name), parent(parent) {}
	Term _thm(char const* name) const;
	static void* _root_init;
public:
	static Ctxt root();
	char const* const name;
	Ctxt const* const parent;
	set<string> const syms() const {
		return _syms;
	}
	vector<string> const sym_list() const {
		return _sym_list;
	}
	/**
	 * @brief Returns the set of assumptions.
	 */
	vector<Term> const assms() const {
		return _assms;
	}
	map<string, Term const> thms() const {
		return _thms;
	}
	/**
	 * @brief Fixes a symbol in the context.
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
	 * @brief Tests if a symbol is fixed in the context.
	 * @return NULL if the symbol is not fixed.
	 * @return pointer to the context which fixes the symbol.
	 */
	Ctxt const* fixes(char const* sym) const;
	/**
	 * @brief Obtains a named theorem from the context or an ancestor.
	 * @exception TheoremNotFound is thrown if the name doesn't match any.
	 */
	Thm thm(char const* name) const;
	Ctxt branch(char const* name = NULL) const {
		return Ctxt(name,this);
	}
};

Ctxt const* Ctxt::fixes(char const* sym) const {
	if( _syms.find(sym) != _syms.end() ) {// already fixed
		return this;
	}
	if( parent == NULL ) {
		return NULL;
	}
	return parent->fixes(sym);
}

Ctxt& Ctxt::fix(char const* sym) {
	if( fixes(sym) == NULL ) {
		_syms.insert(sym);
		_sym_list.push_back(sym);
	}
	return *this;
}
Ctxt& Ctxt::assume(char const* name, Term const& assm) {
	for( auto sym : assm.syms() ) {
		fix(sym.c_str());
	}
	_assms.push_back(assm);
	_thms.insert({name,assm});
	return *this;
}

ostream& operator<<(ostream& os, Ctxt const& ctxt) {
	if( ctxt.name != NULL ) {
		os << "ctxt " << ctxt.name << " {" << endl;
	} else {
		os << "ctxt {" << endl;
	}
	for( auto sym : ctxt.sym_list() ) {
		os << "  sym " << sym << endl;
	}
	for( auto assm : ctxt.assms() ) {
		os << "  assm " << assm << endl;
	}
	for( auto thm : ctxt.thms() ) {
		os << "  thm " << thm.first << ": " << thm.second << endl;
	}
	os << "}" << endl;
	return os;
}

Ctxt Ctxt::root() {
	return Ctxt().fix("⟹").fix("∀").fix("∧");
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
/**
 * @brief Obtains the claim of a theorem, accessible from the context.
 */
Term Ctxt::_thm(char const* name) const {
	auto const& it = _thms.find(name);
	if( it == _thms.end() ) {
		if( parent == NULL ) {
			throw TheoremNotFound();
		}
		return parent->_thm(name);
	}
	return it->second;
}
Thm Ctxt::thm(char const* name) const {
	return Thm(this,_thm(name));
}
Ctxt& Ctxt::claim(char const* name, Thm const& thm) {
	if( thm.ctxt() != this ) {
		throw WrongContext();
	}
	_thms.insert({name,thm});
	return *this;
}

Term const IMP = Term("⟹");

Term operator>>=(Term const& l, Term const& r) {
	return IMP(l)(r);
}

Term const ALL = Term("∀");

Term operator%=(char const* var, Term const& body) {
	return ALL(var /= body);
}

Thm Thm::of(Term const& t) const {
	if( type() != APP || fun() != ALL || arg().type() != ABS ) {
		throw MalformedInstantiation();
	}
	return Thm(_ctxt,arg().body().subst(arg().var(),t));
}

Thm Thm::OF(Thm const& t) const {
	if( t._ctxt != _ctxt ) {
		throw WrongContext();
	}
	if( type() != APP || fun().type() != APP || fun().fun() != IMP || fun().arg() != t ) {
		throw MalformedDischarge();
	}
	return Thm(_ctxt,arg());
}

Thm Thm::lift() const {
	if( _ctxt == NULL ) {
		return *this;
	}
	Term claim = *this;
	auto const& assms = _ctxt->assms();
	for( auto it = assms.rbegin(); it != assms.rend(); it++ ) {
		Term next = *it >>= claim;
		claim = next;
	}
	auto const& syms = _ctxt->sym_list();
	for( auto it = syms.rbegin(); it != syms.rend(); it++ ) {
		claim = it->c_str() %= claim;
	}
	return Thm(_ctxt->parent,claim);
}

ostream& operator<<(ostream& os, Thm const& t) {
	if( t.ctxt()->name != NULL ) {
		os << "(in " << t.ctxt()->name << ") ";
	}
	return os << (Term const)t;
}

Term const EQ = Term("=");

Term operator^(Term const& l, Term const& r) {
	return EQ(l)(r);
}

Term const AND = Term("∧");

Term operator&&(Term const& l, Term const& r) {
	return AND(l)(r);
}

Term const DEFINED = Term("defined");

/*
Ctxt definitional = equational.branch().
	assume("defined.defined",DEFINED(DEFINED)).
	assume("IMP.defined",DEFINED(IMP)).
	assume("ALL.defined",DEFINED(ALL)).
	assume("EQ.defined",DEFINED(EQ));
*/

int main() {
	Term x = Term("x");
	Term y = Term("y");
	Term z = Term("z");
	Term f = Term("f");
	Term g = Term("g");
	Ctxt root = Ctxt::root().
		assume("AND.intro", "x" %= "y" %= (x >>= y >>= x && y)).
		assume("AND.elim", "x" %= "y" %= (x && y) >>= "z" %= (x >>= y >>= z) >>= z).
		assume("EQ.refl", "x" %= x ^ x).
		assume("EQ.trans", "x" %= "y" %= "z" %= x ^ y >>= y ^ z >>= x ^ z).
		assume("EQ.sym", "x" %= "y" %= x ^ y >>= y ^ x).
		assume("EQ.cong", "f" %= "g" %= "x" %= "y" %= f ^ g >>= x ^ y >>= f(x) ^ g(y));


	Ctxt local = root.branch();
	Term P = Term("P");
	Term Q = Term("Q");
	local.assume("p",P);
	root.claim("refl",local.thm("p").lift());
	local.assume("pq",P>>=Q);
	cout << local << endl;
	Thm mp = local.thm("pq").OF(local.thm("p")).lift();
	root.claim("mp",mp);
	cout << root << endl;
	Ctxt local2 = root.branch();
	local2.assume("p_pq", P && (P >>= Q));
	Thm t = local2.thm("AND.elim");
	cout << t << endl;
	t = t.of(P);
	cout << t << endl;
	t = t.of(P >>= Q);
	cout << t << endl;
	t = t.OF(local2.thm("p_pq"));
	cout << t << endl;
	t = t.of(Q);
	cout << t << endl;
	t = t.OF(local2.thm("mp").of(P).of(Q));
	cout << t << endl;
	root.claim("mp2",t.lift());
	cout << root.thm("mp2")<<endl;
}
