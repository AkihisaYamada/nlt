#include<cstring>
#include"core.hpp"

using namespace std;

String avoid(String const& var, function<bool(String const&)> const& test) {
	if( !test(var) ) {
		return var;
	}
	string str = var;
	do {
		str.append("'");
	} while( test(str) );
	return str;
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
	case SYM: _un.sym.~String(); break;
	case APP: _un.app.~App(); break;
	case ABS: _un.abs.~Abs(); break;
	case BIND: _un.fix.~Bind(); break;
	default: assert(false);
	}
}

bool Term::_eq_var(String const& x, String const& y, StrMap<unsigned int>& lmap, StrMap<unsigned int>& rmap ) {
	auto lit = lmap.find(x);
	auto rit = rmap.find(y);
	if( lit != lmap.end() ) {
		return rit != rmap.end() && lit->second == rit->second;
	}
	return rit == rmap.end() && x == y;
}
bool Term::_eq(Term const& l, Term const& r, StrMap<unsigned int>& lmap, StrMap<unsigned int>& rmap, unsigned int depth) {
	if( l._type != r._type ) {
		return false;
	}
	switch(l._type) {
		case SYM:
			return _eq_var(l._un.sym,r._un.sym,lmap,rmap);
		case APP:
			return _eq(l._un.app->first,r._un.app->first,lmap,rmap,depth) &&
				_eq(l._un.app->second,r._un.app->second,lmap,rmap,depth);
		case ABS: {
			auto& labs = *l._un.abs;
			auto& rabs = *r._un.abs;
			depth++;
			auto const& linfo = lmap.insert({labs.first,depth});
			unsigned int lprev;
			if( linfo.second ) {
				lprev = 0;
			} else {
				lprev = linfo.first->second;
				linfo.first->second = depth;
			}
			auto const& rinfo = rmap.insert({rabs.first,depth});
			unsigned int rprev;
			if( rinfo.second ) {
				rprev = 0;
			} else {
				rprev = rinfo.first->second;
				rinfo.first->second = depth;
			}
			if( _eq(labs.second,rabs.second,lmap,rmap,depth) ) {
				if( lprev == 0 ) {
					lmap.erase(linfo.first);
				} else {
					linfo.first->second = lprev;
				}
				if( rprev == 0 ) {
					rmap.erase(rinfo.first);
				} else {
					rinfo.first->second = rprev;
				}
				return true;
			}
			return false;
		}
		case BIND: {
			auto& lfix = *l._un.fix;
			auto& rfix = *r._un.fix;
			return _eq_var(lfix.first,rfix.first,lmap,rmap) &&
				_eq(lfix.second,rfix.second,lmap,rmap,depth);
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
			_un.app->first._iter_syms(bsyms,bsym,fsym);
			_un.app->second._iter_syms(bsyms,bsym,fsym);
			return;
		case ABS: {
			auto& abs = *_un.abs;
			bsyms.insert(abs.first);
			abs.second._iter_syms(bsyms,bsym,fsym);
			bsyms.erase(abs.first);
			return;
		}
		case BIND: {
			auto& fix = *_un.fix;
			if( bsyms.contains(fix.first) ) {
				bsym(fix.first);
			} else {
				fsym(fix.first);
			}
			fix.second._iter_syms(bsyms,bsym,fsym);
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

CSubst& CSubst::_assign(String const& var, CTerm const& val) {
	auto const& info = _map.insert({var,val});
	if( !info.second ) {
		info.first->second = val;
	}
	return *this;
}

Term Term::subst(CSubst const& subst) const {
	StrMap<String> bsyms;
	auto f = [&](String const& sym) {
		auto opt = subst.get(sym);
		return opt.has_value() ? (Term)*opt : sym;
	};
	auto fixed = [&](String const& sym) {
		return subst.ctxt().find(sym).has_value();
	};
	return map(f,fixed,bsyms);
}

static Term subst_var(function<Term(String const&)> f, String const& sym, StrMap<String>& bsyms) {
	for( auto p : bsyms ) {// bound variables should be renamed
		if( p.first == sym ) {
			return p.second;
		}
	}
	return f(sym);
}

Term Term::map(function<Term(String const&)> f, std::function<bool(String const&)> fixed, StrMap<String>& bsyms) const {
	switch(_type) {
		case SYM: return subst_var(f,_un.sym,bsyms);
		case APP: return _un.app->first.map(f,fixed,bsyms)(_un.app->second.map(f,fixed,bsyms));
		case ABS: {
			auto& abs = *_un.abs;
			String const& newvar = avoid(abs.first,[&](String const& x){ return bsyms.contains(x) || fixed(x); });
			auto info = bsyms.insert({abs.first,newvar});
			String prev;
			if( !info.second ) {
				prev = info.first->second;
			}
			Term const& body = abs.second.map(f,fixed,bsyms);
			if( info.second ) {
				bsyms.erase(info.first);
			} else {
				info.first->second = prev;
			}
			return newvar /= body;
		}
		case BIND: {
			auto& fix = *_un.fix;
			Term newbox = subst_var(f,fix.first,bsyms);
			Term newval = fix.second.map(f,fixed,bsyms);
			switch(newbox._type) {
				case SYM: return newbox._un.sym / newval;
				case ABS: return newbox._un.abs->second.subst(newbox._un.abs->first,newval);
				default: throw UnexpectedTerm(newbox);
			}
		}
		default: assert(false);
	}
}

String const VOID_var = String("");
String const IMP_var = String("⟹");
String const ALL_var = String("∀");
Term const IMP = Term(IMP_var);
Term const ALL = Term(ALL_var);

optional<String const> Ctxt::find_local(String const& sym) const {
	auto it = _ref->syms.find(sym);
	if( it != _ref->syms.end() ) {
		return *it;
	}
	auto it2 = _ref->specs.find(sym);
	if( it2 != _ref->specs.end() ) {
		return it2->first;
	}
	return optional<String const>();
}

optional<String const> Ctxt::find(String const& sym) const {
	auto opt = find_local(sym);
	if( !opt.has_value() && _ref->parent.has_value() ) {
		return _ref->parent->find(sym);
	}
	return opt;
}

CTerm Ctxt::fix(String const& sym) const {
	auto opt = find(sym);
	if( opt.has_value() ) {
		return CTerm(*this,*opt);
	}
	_ref->syms.insert(sym);
	_ref->sym_list.push_back(sym);
	return CTerm(*this,sym);
}
CTerm Ctxt::enclose(Term const& t) {
	t.iter_syms(
		[](String const& sym){},// do nothing on bound ones
		[this](String const& sym){ fix(sym); }// fix free symbols
	);
	return CTerm(*this,t);
}
CTerm Ctxt::cterm(Term const& t) const {
	t.iter_syms(
		[](String const& sym){},
		[&](String const& sym){ if( !find(sym).has_value() ) { throw UnboundVariable(sym); } }
	);
	return CTerm(*this,t);
}
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
	if( find(sym) ) {
		throw DoubleFix(sym);
	}
	String thesis = avoid("thesis",[&](String const& x){ return find(x) || sym == x; });
	Term goal = thesis %= (sym %= spec >>= thesis) >>= thesis;
	_ref->specs.insert({sym,spec});
	return pair(goal,Thm(CTerm(*this,goal >>= spec)));
}

Thm Thm::allE(CTerm const& t) const {
	if( t.ctxt() != ctxt() ) {
		throw WrongContext();
	}
	auto a = all();
	if( a.has_value() ) {
		return CTerm(ctxt(),a->second.subst(a->first,t));
	}
	throw MalformedInstantiation(*this,t);
}

Thm Thm::impE(Thm const& t) const {
	if( t.ctxt() != ctxt() ) {
		throw WrongContext();
	}
	auto a = imp();
	if( a.has_value() && a->first == t ) {
		return CTerm(ctxt(),a->second);
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
	return Thm(CTerm(*parent,stmt)).lift(ctxt);
}
CTerm CTerm::weaken(Ctxt const& ctxt) const {
	Ctxt cur = ctxt;
	for(;;) {
		if( cur == _ctxt ) {
			return CTerm(ctxt,*this);
		}
		auto const& parent = cur.parent();
		if( !parent.has_value() ) {
			throw WrongContext();
		}
		cur = *parent;
	}
}
CTerm CTerm::lift(CSubst const& subst) const {
	auto const& parent_opt = _ctxt.parent();
	if( !parent_opt.has_value() ) {
		throw WrongContext();
	}
	Ctxt const& parent = *parent_opt;
	if( parent != subst.ctxt() ) {
		throw WrongContext();
	}
	auto f = [&](String const& sym)->Term {
		auto opt = subst.get(sym);
		if( opt.has_value() ) {
			return *opt;
		}
		auto const& opt2 = parent.find(sym);
		if( opt2.has_value() ) {
			return *opt2;
		}
		throw UnboundVariable(sym);
	};
	auto fixed = [&](String const& sym) {
		return subst.ctxt().find(sym).has_value();
	};
	StrMap<String> bsyms;
	return CTerm(parent,map(f,fixed,bsyms));
}
