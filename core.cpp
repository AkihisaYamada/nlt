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
		case FIX: return Union(_un.fix);
		default: assert(false);
	}
}

Term::~Term() {
	switch(_type) {
	case APP: _un.app.~Ref(); break;
	case ABS: _un.abs.~Ref(); break;
	case FIX: _un.abs.~Ref(); break;
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
			return strcmp(rename_sym(lmap,_un.sym), rename_sym(rmap,other._un.sym)) == 0;
		case APP: {
			auto l = *_un.app, r = *other._un.app;
			return l.fun._eq(r.fun,lmap,rmap,vars) && l.arg._eq(r.arg,lmap,rmap,vars);
		}
		case ABS: {
			auto l = *_un.abs, r = *other._un.abs;
			// replace the bound variables with fresh one and compare
			char const* fresh = vars.make();
			lmap.insert({l.var,fresh});
			rmap.insert({r.var,fresh});
			return l.body._eq(r.body,lmap,rmap,vars);
		}
		case FIX: {
			auto l = *_un.fix, r = *other._un.fix;
			return strcmp(rename_sym(lmap,l.var), rename_sym(rmap,r.var)) == 0 &&
				l.val._eq(r.val,lmap,rmap,vars);
		}
		default: assert(false);
	}
}

void Term::_iter_syms(Syms& bsyms, function<void(char const*)> const& bsym, function<void(char const*)> const& fsym) const {
	switch(_type) {
		case SYM: {
			auto x = _un.sym;
			if( bsyms.find(x) == bsyms.end() ) {
				fsym(x);
			} else {
				bsym(x);
			}
			return;
		}
		case APP: {
			auto x = *_un.app;
			x.fun._iter_syms(bsyms,bsym,fsym);
			x.arg._iter_syms(bsyms,bsym,fsym);
			return;
		}
		case ABS: {
			auto x = *_un.abs;
			bsyms.insert(x.var);
			x.body._iter_syms(bsyms,bsym,fsym);
			return;
		}
		case FIX: {
			auto x = *_un.fix;
			if( bsyms.find(x.var) == bsyms.end() ) {
				fsym(x.var);
			} else {
				bsym(x.var);
			}
			x.val._iter_syms(bsyms,bsym,fsym);
			return;
		}
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
			auto s = _un.sym;
			if( strcmp(x,s) == 0 ) {
				return val;
			}
			auto it = ren.find(s);
			if( it == ren.end() ) {
				return *this;
			}
			return Term(it->second);
		}
		case APP: {
			auto s = *_un.app;
			return s.fun._subst(x,val,ren,fixed,vars)(s.arg._subst(x,val,ren,fixed,vars));
		}
		case ABS: {
			auto s = *_un.abs;
			if( strcmp(s.var, x) == 0 ) {// the variable is captured. Just apply necessary renaming.
				return x /= s.body._subst(x,Term(x),ren,fixed,vars);
			}
			// if the bound variable is fixed, rename to a fresh one.
			bool must_rename = fixed(s.var);
			char const* newvar = must_rename ? vars.make() : s.var;
			if( must_rename ) {
				ren.insert({s.var,newvar});
			}
			Term ret = newvar /= s.body._subst(x,val,ren,fixed,vars);
			ren.erase(s.var);
			return ret;
		}
		case FIX: {
			auto s = *_un.fix;
			Term newval = s.val._subst(x,val,ren,fixed,vars);
			if( strcmp(s.var,x) == 0 ) {
				switch(val._type) {
					case SYM: {
						return val._un.sym / newval;
					}
					case ABS: {
						auto a = *val._un.abs;
						return a.body.subst(a.var,newval,fixed);
					}
					default:
						throw UnexpectedTerm();
				}
			}
			return s.var / newval;
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
	auto a = app();
	if( a != NULL && a->fun == ALL ) {
		auto b = a->arg.abs();
		if( b != NULL ) {
			return Thm(_ctxt,b->body.
				subst(b->var, t, [&](char const* sym){ return _ctxt->fixes(sym); }));
		}
	}
	cerr << "ERROR: Instantiating " << *this << endl;
	throw MalformedInstantiation();
}

Thm Thm::OF(Thm const& t) const {
	if( t._ctxt != _ctxt ) {
		cerr << "ERROR: Discharging with wrong contexts " << *this << endl;
		throw WrongContext();
	}
	auto a = app();
	if( a != NULL ) {
		auto b = a->fun.app();
		if( b != NULL && b->fun == IMP && b->arg == t ) {
			return Thm(_ctxt,a->arg);
		}
	}
	cerr << "ERROR: Discharging\n\t" << *this << endl << "\nwith\t" << t << endl;
	throw MalformedDischarge();
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


ostream& operator<<(ostream& os, Term const& t) {
	{	auto sym = t.sym();
		if( sym != NULL ) {
			return os << *sym;
		}
	}
	{	auto app = t.app();
		if( app != NULL ) {
			return os << '(' << app->fun << ' ' << app->arg << ')';
		}
	}
	{	auto abs = t.abs();
		if( abs != NULL ) {
			return os << abs->var << ". " << abs->body;
		}
	}
	{	auto fix = t.fix();
		if( fix != NULL ) {
			return os << fix->var << "[" << fix->val << "]";
		}
	}
	assert(false);
};

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

ostream& operator<<(ostream& os, Thm const& t) {
	if( t.ctxt()->name != NULL ) {
		os << "(in " << t.ctxt()->name << ") ";
	}
	return os << (Term const)t;
}
