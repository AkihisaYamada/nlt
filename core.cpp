#include<cstring>
#include"core.hpp"

using namespace std;

vector<String> VarMaker::vec;

String VarMaker::make() {
	auto pre = nest;
	nest++;
	if( pre < vec.size() ) {
		return vec[pre];
	}
	// permanently allocate a string.
	String name = string("_") + to_string(nest);
	vec.push_back(name);
	return name;
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

Term::Term(Term const& other) : _type(other._type), _un(other._copy_un()) {}

Term::~Term() {
	switch(_type) {
	case SYM: _un.sym.~String(); break;
	case APP: _un.app.fun.~Ref(); _un.app.arg.~Ref(); break;
	case ABS: _un.abs.var.~String(); _un.abs.body.~Ref(); break;
	case BIND: _un.fix.var.~String(); _un.fix.val.~Ref(); break;
	default: assert(false);
	}
}

static inline String rename_sym(Renaming const& map, String const& sym) {
	auto const& it = map.find(sym);
	return it == map.end() ? sym : it->second;
}

bool Term::_eq(Term const& other, Renaming& lmap, Renaming& rmap, VarMaker vars) const {
	if( _type != other._type ) {
		return false;
	}
	switch(_type) {
		case SYM: {
			return rename_sym(lmap,_un.sym) == rename_sym(rmap,other._un.sym);
		}
		case APP: {
			return _un.app.fun->_eq(*other._un.app.fun,lmap,rmap,vars) &&
				_un.app.arg->_eq(*other._un.app.arg,lmap,rmap,vars);
		}
		case ABS: {
			// replace the bound variables with fresh one and compare
			auto const& fresh = vars.make();
			lmap[_un.abs.var] = fresh;
			rmap[other._un.abs.var] = fresh;
			return _un.abs.body->_eq(*other._un.abs.body,lmap,rmap,vars);
		}
		case BIND: {
			return rename_sym(lmap,_un.fix.var) == rename_sym(rmap,other._un.fix.var) &&
				_un.fix.val->_eq(*other._un.fix.val,lmap,rmap,vars);
		}
		default: assert(false);
	}
}

void Term::_iter_syms(
	Syms& bsyms,
	function<void(String const&)> const& bsym,
	function<void(String const&)> const& fsym
) const {
	switch(_type) {
		case SYM:
			if( bsyms.contains(_un.sym) ) {
				bsym(_un.sym);
			} else {
				fsym(_un.sym);
			}
			return;
		case APP:
			_un.app.fun->_iter_syms(bsyms,bsym,fsym);
			_un.app.arg->_iter_syms(bsyms,bsym,fsym);
			return;
		case ABS: {
			auto& var = _un.abs.var;
			bsyms.insert(var);
			_un.abs.body->_iter_syms(bsyms,bsym,fsym);
			bsyms.erase(var);
			return;
		}
		case BIND: {
			auto& var = _un.fix.var;
			if( bsyms.contains(var) ) {
				bsym(var);
			} else {
				fsym(var);
			}
			_un.fix.val->_iter_syms(bsyms,bsym,fsym);
			return;
		}
		default: assert(false);
	}
}

Syms Term::fsyms() const {
	Syms bsyms, ret;
	_iter_syms(bsyms,[](String const&){},[&ret](String const& fsym){ret.insert(fsym);});
	return ret;
}

Term Term::_subst(
	String const& x,
	Term const& val,
	Renaming& ren,
	Syms const& fixed,
	VarMaker vars
) const {
	switch(_type) {
		case SYM: {
			if( x == _un.sym ) {
				return val;
			}
			auto it = ren.find(_un.sym);
			return it == ren.end() ? *this : Term(it->second);
		}
		case APP: {
			return _un.app.fun->_subst(x,val,ren,fixed,vars)(_un.app.arg->_subst(x,val,ren,fixed,vars));
		}
		case ABS: {
			auto& var = _un.abs.var;
			if( var == x ) {// the variable is captured. Just apply necessary renaming.
				return var /= _un.abs.body->_subst(var,Term(var),ren,fixed,vars);
			}
			// if the bound variable is fixed, rename to a fresh one.
			bool must_rename = fixed.contains(var);
			String const& newvar = must_rename ? vars.make() : var;
			if( must_rename ) {
				ren[var] = newvar;
			}
			Term ret = newvar /= _un.abs.body->_subst(x,val,ren,fixed,vars);
			ren.erase(var);
			return ret;
		}
		case BIND: {
			auto& var = _un.fix.var;
			Term newval = _un.fix.val->_subst(x,val,ren,fixed,vars);
			if( var == x ) {
				switch(val._type) {
					case SYM:
						return val._un.sym / newval;
					case ABS:
						return val._un.abs.body->subst(val._un.abs.var,newval);
					default:
						throw UnexpectedTerm(*this);
				}
			}
			return var / newval;
		}
		default: assert(false);
	}
}

String const VOID_var = String("");
String const IMP_var = String("⟹");
String const ALL_var = String("∀");
Term const IMP = Term(IMP_var);
Term const ALL = Term(ALL_var);

Ctxt::Ctxt() : _ref(Body{}) {
	fix(IMP_var);
	fix(ALL_var);
}

bool Ctxt::fixes(String const& sym) const {
	return syms().contains(sym) ||
		specs().contains(sym) ||
		parent() && parent()->fixes(sym);
}

Ctxt const& Ctxt::fix(String const& sym) const {
	if( !fixes(sym) ) {
		_ref->syms.insert(sym);
		_ref->sym_list.push_back(sym);
	}
	return *this;
}

void Ctxt::_add_thm(String const& name, Term const& stmt) const {
	stmt.iter_syms(
		[](String const& sym){},// do nothing on bound ones
		[this](String const& sym){ fix(sym); }// fix free symbols
	);
	_ref->thms.insert({name,stmt});
}


/**
 * @brief Obtains the claim of a theorem, accessible from the context.
 */
Term Ctxt::_thm(String const& name) const {
	auto const& it = _ref->thms.find(name);
	if( it == _ref->thms.end() ) {
		if( !_ref->parent ) {
			throw TheoremNotFound(name);
		}
		return _ref->parent->_thm(name);
	}
	return it->second;
}

pair<Term,Thm> Ctxt::obtain(String const& sym, Term const& spec) const {
	if( fixes(sym) ) {
		throw DoubleFix(sym);
	}
	VarMaker varmaker;
	auto const& thesis = varmaker.make();
	Term goal = thesis %= (sym %= spec >>= Term(thesis)) >>= Term(thesis);
	_ref->specs.insert({sym,spec});
	return pair(goal,Thm(*this,goal >>= spec));
}

Thm Thm::allE(Term const& t) const {
	auto a = all();
	if( a.has_value() ) {
		return Thm(ctxt(),a->second.subst(a->first,t));
	}
	throw MalformedInstantiation(*this,t);
}

Thm Thm::impE(Thm const& t) const {
	if( t.ctxt() != ctxt() ) {
		throw WrongContext();
	}
	auto a = imp();
	if( a.has_value() && a->first == t ) {
		return Thm(ctxt(),a->second);
	}
	throw MalformedDischarge(*this,t);
}

Thm Thm::lift(Ctxt const& ctxt) const {
	if( ctxt == _ctxt ) {
		return *this;
	}
	auto const& parent = _ctxt.parent();
	if( !parent.has_value() ) {
		throw WrongContext();
	}
	Term stmt = *this;
	auto const& assms = _ctxt.assms();
	for( auto it = assms.rbegin(); it != assms.rend(); it++ ) {
		stmt = *it >>= stmt;
	}
	auto const& syms = _ctxt.sym_list();
	for( auto it = syms.rbegin(); it != syms.rend(); it++ ) {
		stmt = *it %= stmt;
	}
	return Thm(*parent,stmt);
}
Thm Thm::weaken(Ctxt const& ctxt) const {
	Ctxt cur = ctxt;
	for(;;) {
		if( cur == _ctxt ) {
			return Thm(ctxt,*this);
		}
		auto const& parent = cur.parent();
		if( !parent.has_value() ) {
			throw WrongContext();
		}
		cur = *parent;
	}
}