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

static bool _eq_var(String const& x, String const& y, StrMap<unsigned int>& lmap, StrMap<unsigned int>& rmap ) {
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
	auto f = [&](String const& sym) {
		auto opt = subst.get(sym);
		return opt.has_value() ? (Term)*opt : sym;
	};
	auto fixed = [&](String const& sym) {
		return subst.ctxt().find_sym(sym).has_value();
	};
	return map(f,fixed);
}

static Term subst_var(function<Term(String const&)> f, String const& sym, StrMap<String>& bsyms) {
	auto const& it = bsyms.find(sym);
	if( it != bsyms.end() ) {
		return it->second;
	}
	return f(sym);
}

Term Term::_map(function<Term(String const&)> f, std::function<bool(String const&)> fixed, StrMap<String>& bsyms) const {
	switch(_type) {
		case SYM: return subst_var(f,_un.sym,bsyms);
		case APP: return _un.app->first._map(f,fixed,bsyms)(_un.app->second._map(f,fixed,bsyms));
		case ABS: {
			auto& abs = *_un.abs;
			String var = abs.first;
			Term body = abs.second;
			String const& newvar = avoid(var,[&](String const& x){ return bsyms.contains(x) || fixed(x); });
			auto newvar_info = bsyms.insert({newvar,newvar});// the new name should be avoided
			if( newvar == var ) {// the bound variable is fresh
				body = body._map(f,fixed,bsyms);
			} else {
				// replace the original name
				auto replace_info = bsyms.insert({abs.first,newvar});
				String prev;
				if( !replace_info.second ) {// the variable is bound multiple times
					prev = replace_info.first->second;// remember the old assignment
					replace_info.first->second = newvar;// update to the new name
				}
				body = body._map(f,fixed,bsyms);
				// forget/recover replacement
				if( replace_info.second ) {
					bsyms.erase(replace_info.first);
				} else {
					replace_info.first->second = prev;
				}
			}
			// release the new name
			bsyms.erase(newvar_info.first);
			return newvar /= body;
		}
		case BIND: {
			auto& fix = *_un.fix;
			Term newbox = subst_var(f,fix.first,bsyms);
			Term newval = fix.second._map(f,fixed,bsyms);
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

optional<String const> Ctxt::find_sym_local(String const& sym) const {
	auto it = _ref->syms.find(sym);
	if( it != _ref->syms.end() ) {
		return *it;
	}
	return optional<String const>();
}

optional<String const> Ctxt::find_sym(String const& sym) const {
	auto opt = find_sym_local(sym);
	if( !opt.has_value() ) {
		auto const& parent = find_ctxt();
		if( parent.has_value() ) {
			return parent->find_sym(sym);
		}
	}
	return opt;
}

CTerm Ctxt::fix(String const& sym) {
	auto opt = find_sym(sym);
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
		[&](String const& sym){ if( !find_sym(sym).has_value() ) { throw UnboundVariable(sym); } }
	);
	return CTerm(*this,t);
}
Term Ctxt::_thm(String const& name) const {
	auto const& it = _ref->thms.find(name);
	if( it == _ref->thms.end() ) {
		auto const& parent = find_ctxt();
		if( !parent.has_value() ) {
			throw TheoremNotFound(name);
		}
		return parent->_thm(name);
	}
	return it->second;
}

Ctxt Ctxt::obtain(String const& sym, std::vector<std::pair<String,Term>> const& specs) {
	if( find_sym(sym) ) {
		throw DoubleFix(sym);
	}
	Ctxt ret = branch();
	String thesis = avoid("thesis",[&](String const& x){ return find_sym(x) || sym == x; });
	Term assm = thesis;
	ret.fix(sym);
	for( auto it = specs.rbegin(); it != specs.rend(); it++ ) {
		ret.cterm(it->second);// check closedness
		assm = it->second >>= assm;
		ret._ref->thms.insert(*it);
	}
	assm = ALL( thesis /= ALL( sym /= assm ) >>= thesis );
	ret._ref->assms.push_back(assm);
	return ret;
}
Thm Thm::_allE(CTerm const& t) const {
	auto const& a = app();
	if( a.has_value() && a->first == ALL ) {
		return a->second.inst(t);
	}
	throw MalformedInstantiation(*this,t);
}

Thm Thm::impE(Thm const& t) const {
	if( t.ctxt() != ctxt() ) {
		throw WrongContext();
	}
	auto const& app1 = app();
	if( app1.has_value() ) {
		auto const& app2 = app1->first.app();
		if( app2->first == IMP && app2->second == t ) {
			return app1->second;
		}
	}
	throw MalformedDischarge(*this,t);
}

Thm Thm::intro() const {
	auto const& parent = _ctxt.ctxt();
	Term stmt = *this;
	auto const& assms = _ctxt.assms();
	for( auto it = assms.rbegin(); it != assms.rend(); it++ ) {
		stmt = *it >>= stmt;
	}
	auto const& syms = _ctxt.sym_list();
	for( auto it = syms.rbegin(); it != syms.rend(); it++ ) {
		stmt = ALL(*it /= stmt);
	}
	return Thm(CTerm(parent,stmt));
}
std::optional<CTerm::StrTerm> CTerm::abs() const {
	auto const& tabs = Term::abs();
	if( !tabs.has_value() ) {
		return std::optional<StrTerm>();
	}
	String const& var = tabs->first;
	Term const& body = tabs->second;
	Ctxt loc = _ctxt.branch();
	loc.fix(var);
	return StrTerm(var,CTerm(loc,body));
}
CTerm CTerm::lift() const {
	auto const& parent = _ctxt.ctxt();
	Term ret = *this;
	for( auto const& sym : _ctxt.sym_list() ) {
		ret = sym /= ret;
	}
	return CTerm(parent,ret);
}

CTerm CTerm::subst(CSubst const& subst) const {
	auto const& ctxt = subst.ctxt();
	_ctxt.ensure_ancestor(ctxt);
	auto f = [&](String const& sym)->Term {
		auto const& opt = subst.get(sym);
		if( opt.has_value() ) {
			return *opt;
		}
		auto const& opt2 = ctxt.find_sym(sym);
		if( opt2.has_value() ) {
			return *opt2;
		}
		throw UnboundVariable(sym);
	};
	auto fixed = [&](String const& sym) {
		return subst.ctxt().find_sym(sym).has_value();
	};
	return CTerm(ctxt,map(f,fixed));
}
Ctxt Ctxt::interpret(CSubst const& subst, std::vector<Thm> const& facts) const {
	auto const& parent = ctxt();
	if( subst.ctxt() != parent ) {
		throw WrongContext();
	}
	Ctxt ret = parent.branch();
	for( auto& sym : syms() ) {// fix uninstantiated variables
		if( !subst.map().contains(sym) ) {
			ret.fix(sym);
		}
	}
	auto it = facts.begin();
	for( auto& assm : assms() ) {// check that the instances of assumptions are discharged
		if( it == facts.end() ) {
			throw MalformedDischarge(assm,Term());
		}
		if( it->ctxt() != parent ) {
			throw WrongContext();
		}
		Term const& goal = assm.subst(subst);
		if( *it != goal ) {
			throw MalformedDischarge(goal,*it);
		}
		it++;
	}
	for( auto& thm : thms() ) {
		ret._ref->thms.insert({thm.first,thm.second.subst(subst)});
	}
	return ret;
}
Ctxt& Ctxt::import(Ctxt const& ctxt) {
	auto const& parent = ctxt.find_ctxt();
	if( parent.has_value() ) {
		ensure_ancestor(*parent);
	}
	for( auto& sym : ctxt.sym_list() ) {
		fix(sym);
	}
	for( auto& assm : ctxt.assms() ) {
		_ref->assms.push_back(assm);
	}
	for( auto& thm : ctxt.thms() ) {
		_ref->thms.insert(thm);
	}
	return *this;
}

