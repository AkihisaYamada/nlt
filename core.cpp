#include"core.hpp"

using namespace std;

vector<char const*> Term::VarMaker::vec;

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
	}
}

void Term::_iter_syms(Syms& bsyms, function<void(char const*)> bsym, function<void(char const*)> fsym) const {
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
	}
}

Syms Term::fsyms() const {
	Syms bsyms, ret;
	_iter_syms(bsyms,[](char const*){},[&ret](char const* fsym){ret.insert(fsym);});
	return ret;
}

Term Term::_subst(Subst& map, Syms const& csyms, VarMaker vars) const {
	switch(_type) {
		case SYM:
			return subst_sym(map,sym());
		case APP:
			return fun()._subst(map,csyms,vars)(arg()._subst(map,csyms,vars));
		case ABS: {
			char const* newvar =
				csyms.find(var()) == csyms.end() ? var() : vars.make();
			auto it = map.find(var());
			if( it != map.end() ) {
				Term old = it->second;
				map.erase(it);// `[key] = val` requires default constructor
				map.insert({var(),Term(newvar)});
				Term ret = newvar /= body()._subst(map,csyms,vars);
				map.erase(var());
				map.insert({var(),old});
				return ret;
			}
			map.insert({var(),Term(newvar)});
			Term ret = newvar /= body()._subst(map,csyms,vars);
			map.erase(var());
			return ret;
		}
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
	assm.iter_syms(
		[](char const* sym){},// do nothing on bound ones
		[this](char const* sym){ this->fix(sym); }// fix free symbols
	);
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
	return Thm(_ctxt,arg().body().subst({{arg().var(),t}},_ctxt->syms()));
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

ostream& operator<<(ostream& os, Thm const& t) {
	if( t.ctxt()->name != NULL ) {
		os << "(in " << t.ctxt()->name << ") ";
	}
	return os << (Term const)t;
}
