#include"core.hpp"

using namespace std;

vector<char const*> Term::VarMaker::vec;

Term& Term::operator=(Term const& other) {
	Term temp1 = other;// copy other
	char temp2[sizeof *this];
	memcpy(temp2,this,sizeof *this);// remember old this
	memcpy(this,&temp1,sizeof *this);// new this is the copy
	memcpy(&temp1,temp2,sizeof *this);// temp1 is old this, to be destructed
	return *this;
}

Term::Union Term::_copy_un() const {
	switch(_type) {
		case SYM: return Union(_un.sym);
		case APP: return Union(_un.app);
		case ABS: return Union(_un.abs);
		default: assert(false);
	}
}

Term::~Term() {
	switch(_type) {
	case APP: _un.app.~Ref(); break;
	case ABS: _un.abs.~Ref(); break;
	case SYM: break;
	default: assert(false);
	}
}

bool Term::_eq(Term const& other, Renaming& lmap, Renaming& rmap, VarMaker vars) const {
	if( _type != other._type ) {
		return false;
	}
	switch(_type) {
		case SYM:
			return strcmp(rename_sym(lmap,sym()), rename_sym(rmap,other.sym())) == 0;
		case APP:
			return fun()._eq(other.fun(),lmap,rmap,vars) &&
				arg()._eq(other.arg(),lmap,rmap,vars);
		case ABS: {
			// replace the bound variables with fresh one and compare
			char const* fresh = vars.make();
			lmap.insert({var(),fresh});
			rmap.insert({other.var(),fresh});
			return body()._eq(other.body(),lmap,rmap,vars);
		}
		default: assert(false);
	}
}

void Term::_iter_syms(Syms& bsyms, function<void(char const*)> const& bsym, function<void(char const*)> const& fsym) const {
	switch(_type) {
		case SYM:
			if( bsyms.find(sym()) == bsyms.end() ) {
				fsym(sym());
			} else {
				bsym(sym());
			}
			return;
		case APP:
			fun()._iter_syms(bsyms,bsym,fsym);
			arg()._iter_syms(bsyms,bsym,fsym);
			return;
		case ABS:
			bsyms.insert(var());
			body()._iter_syms(bsyms,bsym,fsym);
			return;
		default: assert(false);
	}
}

Syms Term::fsyms() const {
	Syms bsyms, ret;
	_iter_syms(bsyms,[](char const*){},[&ret](char const* fsym){ret.insert(fsym);});
	return ret;
}

Term Term::_subst(
	char const* x,
	Term const& val,
	Renaming& ren,
	function<bool(char const*)> const& fixed,
	VarMaker vars
) const {
	switch(_type) {
		case SYM: {
			if( strcmp(x,sym()) == 0 ) {
				return val;
			}
			auto it = ren.find(sym());
			if( it == ren.end() ) {
				return *this;
			}
			return Term(it->second);
		}
		case APP:
			return fun()._subst(x,val,ren,fixed,vars)(arg()._subst(x,val,ren,fixed,vars));
		case ABS: {
			if( var() == x ) {// the variable is captured. Just apply necessary renaming.
				return x /= body()._subst(x,Term(x),ren,fixed,vars);
			}
			// if the bound variable is fixed, rename to a fresh one.
			bool must_rename = fixed(var());
			char const* newvar = must_rename ? vars.make() : var();
			if( must_rename ) {
				ren.insert({var(),newvar});
			}
			Term ret = newvar /= body()._subst(x,val,ren,fixed,vars);
			ren.erase(var());
			return ret;
		}
		default: assert(false);
	}
}

bool Ctxt::fixes(char const* sym) const {
	if( _syms.find(sym) != _syms.end() ) {
		return true;
	}
	if( parent == NULL ) {
		return false;
	}
	return parent->fixes(sym);
}

Ctxt& Ctxt::fix(char const* sym) {
	if( !fixes(sym) ) {
		_syms.insert(sym);
		_sym_list.push_back(sym);
	}
	return *this;
}

Ctxt& Ctxt::assume(char const* name, Term const& assm) {
	assm.iter_syms(
		[](char const* sym){},// do nothing on bound ones
		[this](char const* sym){ this->fix(sym); }// fix free symbols
	);
	_assms.push_back(assm);
	_thms.insert({name,assm});
	return *this;
}

Ctxt::Ctxt(char const* name) : name(name), parent(NULL) {
	fix("⟹");
	fix("∀");
}

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
Ctxt& Ctxt::claim(char const* name, Thm const& thm) {
	if( thm.ctxt() != this ) {
		throw WrongContext();
	}
	_thms.insert({name,thm});
	return *this;
}

Term const IMP = Term("⟹");
Term const ALL = Term("∀");

Thm Thm::of(Term const& t) const {
	if( type() != APP || fun() != ALL || arg().type() != ABS ) {
		throw MalformedInstantiation();
	}
	return Thm(_ctxt,arg().body().
		subst(arg().var(), t, [&](char const* sym){ return _ctxt->fixes(sym); }));
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
		claim = *it %= claim;
	}
	return Thm(_ctxt->parent,claim);
}
