#include"core.hpp"

using namespace std;

vector<string_view> Term::VarMaker::vec;

string_view Term::VarMaker::make() {
	auto pre = nest;
	nest++;
	if( pre < vec.size() ) {
		return vec[pre];
	}
	// permanently allocate a string.
	string const* name = new string("_" + to_string(nest));
	vec.push_back(*name);
	return vec.back();
}

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
		case BIND: return Union(_un.fix);
		default: assert(false);
	}
}

Term::~Term() {
	switch(_type) {
	case SYM: _un.sym.~Ref(); break;
	case APP: _un.app.~Ref(); break;
	case ABS: _un.abs.~Ref(); break;
	case BIND: _un.abs.~Ref(); break;
	default: assert(false);
	}
}

bool Term::_eq(Term const& other, Renaming& lmap, Renaming& rmap, VarMaker vars) const {
	if( _type != other._type ) {
		return false;
	}
	switch(_type) {
		case SYM: {
			auto l = *_un.sym, r = *other._un.sym;
			return rename_sym(lmap,l) == rename_sym(rmap,r);
		}
		case APP: {
			auto l = *_un.app, r = *other._un.app;
			return l.fun._eq(r.fun,lmap,rmap,vars) && l.arg._eq(r.arg,lmap,rmap,vars);
		}
		case ABS: {
			auto l = *_un.abs, r = *other._un.abs;
			// replace the bound variables with fresh one and compare
			string_view fresh = vars.make();
			lmap[l.var] = fresh;
			rmap[r.var] = fresh;
			return l.body._eq(r.body,lmap,rmap,vars);
		}
		case BIND: {
			auto l = *_un.fix, r = *other._un.fix;
			return rename_sym(lmap,l.var) == rename_sym(rmap,r.var) &&
				l.val._eq(r.val,lmap,rmap,vars);
		}
		default: assert(false);
	}
}

void Term::_iter_syms(Syms& bsyms, function<void(string_view)> const& bsym, function<void(string_view)> const& fsym) const {
	switch(_type) {
		case SYM: {
			auto x = *_un.sym;
			if( bsyms.contains(x) ) {
				bsym(x);
			} else {
				fsym(x);
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
			bsyms.erase(x.var);
			return;
		}
		case BIND: {
			auto x = *_un.fix;
			if( bsyms.contains(x.var) ) {
				bsym(x.var);
			} else {
				fsym(x.var);
			}
			x.val._iter_syms(bsyms,bsym,fsym);
			return;
		}
		default: assert(false);
	}
}

Syms Term::fsyms() const {
	Syms bsyms, ret;
	_iter_syms(bsyms,[](string_view){},[&ret](string_view fsym){ret.insert(string(fsym));});
	return ret;
}

Term Term::_subst(
	string_view x,
	Term const& val,
	Renaming& ren,
	Syms const& fixed,
	VarMaker vars
) const {
	switch(_type) {
		case SYM: {
			auto s = *_un.sym;
			if( x == s ) {
				return val;
			}
			auto it = ren.find(s);
			return it == ren.end() ? *this : Term(it->second);
		}
		case APP: {
			auto s = *_un.app;
			return s.fun._subst(x,val,ren,fixed,vars)(s.arg._subst(x,val,ren,fixed,vars));
		}
		case ABS: {
			auto s = *_un.abs;
			if( s.var == x ) {// the variable is captured. Just apply necessary renaming.
				return x /= s.body._subst(x,Term(x),ren,fixed,vars);
			}
			// if the bound variable is fixed, rename to a fresh one.
			bool must_rename = fixed.contains(s.var);
			string_view newvar = must_rename ? vars.make() : s.var;
			if( must_rename ) {
				ren[s.var] = newvar;
			}
			Term ret = newvar /= s.body._subst(x,val,ren,fixed,vars);
			ren.erase(s.var);
			return ret;
		}
		case BIND: {
			auto s = *_un.fix;
			Term newval = s.val._subst(x,val,ren,fixed,vars);
			if( s.var == x ) {
				switch(val._type) {
					case SYM: {
						return *val._un.sym / newval;
					}
					case ABS: {
						auto a = *val._un.abs;
						return a.body.subst(a.var,newval);
					}
					default:
						throw UnexpectedTerm(*this);
				}
			}
			return s.var / newval;
		}
		default: assert(false);
	}
}

Term const IMP = Term("⟹");
Term const ALL = Term("∀");

Ctxt::Ctxt() : _ref(Body{}) {
	fix("⟹");
	fix("∀");
}

bool Ctxt::fixes(string_view sym) const {
	return syms().contains(sym) ||
		parent() && parent()->fixes(sym);
}

Ctxt const& Ctxt::fix(string_view sym) const {
	if( !fixes(sym) ) {
		_ref->syms.insert(string(sym));
		_ref->sym_list.push_back(string(sym));
	}
	return *this;
}

void Ctxt::_add_thm(string_view name, Term const& stmt) const {
	stmt.iter_syms(
		[](string_view sym){},// do nothing on bound ones
		[this](string_view sym){ this->fix(sym); }// fix free symbols
	);
	_ref->thms.insert({string(name),stmt});
}


/**
 * @brief Obtains the claim of a theorem, accessible from the context.
 */
Term Ctxt::_thm(string_view name) const {
	auto const& it = _ref->thms.find(name);
	if( it == _ref->thms.end() ) {
		if( !_ref->parent ) {
			throw TheoremNotFound(name);
		}
		return _ref->parent->_thm(name);
	}
	return it->second;
}

Thm Thm::of(Term const& t) const {
	auto a = all();
	if( a.has_value() ) {
		return Thm(ctxt(),a->second.subst(a->first,t));
	}
	throw MalformedInstantiation(*this,t);
}

Thm Thm::OF(Thm const& t) const {
	if( t.ctxt() != ctxt() ) {
		throw WrongContext();
	}
	auto a = imp();
	if( a.has_value() && a->first == t ) {
		return Thm(ctxt(),a->second);
	}
	throw MalformedDischarge(*this,t);
}

void Ctxt::_quantify_thm(Ctxt const& other, Term& stmt) const {
	if( other == *this ) {
		return;
	}
	if( !other.parent() ) {
		throw WrongContext();
	}
	auto assms = other.assms();
	for( auto it = assms.rbegin(); it != assms.rend(); it++ ) {
		stmt = *it >>= stmt;
	}
	auto syms = other.sym_list();
	for( auto it = syms.rbegin(); it != syms.rend(); it++ ) {
		stmt = *it %= stmt;
	}
	_quantify_thm(*other.parent(),stmt);
}

