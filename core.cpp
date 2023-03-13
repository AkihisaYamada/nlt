#include<cstring>
#include"core.hpp"

using namespace std;

variant<String,Term::App,Term::Abs,Term::Bind> Term::_copy_un() const {
	if( auto p = get_if<String>(&_un) ) {
		return *p;
	} else if( auto p = get_if<App>(&_un) ) {
		return *p;
	} else if( auto p = get_if<Abs>(&_un) ) {
		return *p;
	} else if( auto p = get_if<Bind>(&_un) ) {
		return *p;
	} else {
		assert(false);
	}
}

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

static bool _eq_var(String const& x, String const& y, StrMap<unsigned int>& lmap, StrMap<unsigned int>& rmap ) {
	auto lit = lmap.find(x);
	auto rit = rmap.find(y);
	if( lit != lmap.end() ) {
		return rit != rmap.end() && lit->second == rit->second;
	}
	return rit == rmap.end() && x == y;
}
bool Term::_eq(Term const& l, Term const& r, StrMap<unsigned int>& lmap, StrMap<unsigned int>& rmap, unsigned int depth) {
	if( auto lsym = l.sym() ) {
		if( auto rsym = r.sym() ) {
			return _eq_var(*lsym,*rsym,lmap,rmap);
		}
	} else if( auto lapp = l.app() ) {
		if( auto rapp = r.app() ) {
			return _eq(lapp->first,rapp->first,lmap,rmap,depth) &&
				_eq(lapp->second,rapp->second,lmap,rmap,depth);
		}
	} else if( auto labs = l.abs() ) {
		if( auto rabs = r.abs() ) {
			depth++;
			auto const& linfo = lmap.insert({labs->first,depth});
			unsigned int lprev;
			if( linfo.second ) {
				lprev = 0;
			} else {
				lprev = linfo.first->second;
				linfo.first->second = depth;
			}
			auto const& rinfo = rmap.insert({rabs->first,depth});
			unsigned int rprev;
			if( rinfo.second ) {
				rprev = 0;
			} else {
				rprev = rinfo.first->second;
				rinfo.first->second = depth;
			}
			if( _eq(labs->second,rabs->second,lmap,rmap,depth) ) {
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
		}
	} else if( auto lfix = l.fix() ) {
		if( auto rfix = r.fix() ) {
			return _eq_var(lfix->first,rfix->first,lmap,rmap) &&
				_eq(lfix->second,rfix->second,lmap,rmap,depth);
		}
	} else {
		assert(false);
	}
	return false;
}

void Term::_iter_syms(
	StrSet& bsyms,
	function<void(String const&)> const& bsym,
	function<void(String const&)> const& fsym
) const {
	if( auto sym = this->sym() ) {
		if( bsyms.contains(*sym) ) {
			bsym(*sym);
		} else {
			fsym(*sym);
		}
	} else if( auto app = this->app() ) {
		app->first._iter_syms(bsyms,bsym,fsym);
		app->second._iter_syms(bsyms,bsym,fsym);
	} else if( auto abs = this->abs() ) {
		bsyms.insert(abs->first);
		abs->second._iter_syms(bsyms,bsym,fsym);
		bsyms.erase(abs->first);
	} else if( auto fix = this->fix() ) {
		if( bsyms.contains(fix->first) ) {
			bsym(fix->first);
		} else {
			fsym(fix->first);
		}
		fix->second._iter_syms(bsyms,bsym,fsym);
	} else {
		assert(false);
	}
}

StrSet Term::fsyms() const {
	StrSet bsyms, ret;
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
		return opt ? (Term)*opt : sym;
	};
	auto fixed = [&](String const& sym)->bool {
		return subst.ctxt().find_sym(sym);
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
	if( auto sym = this->sym() ) {
		return subst_var(f,*sym,bsyms);
	} else if( auto app = this->app() ) {
		return app->first._map(f,fixed,bsyms)(app->second._map(f,fixed,bsyms));
	} else if( auto abs = this->abs() ) {
		String var = abs->first;
		Term body = abs->second;
		String const& newvar = avoid(var,[&](String const& x){ return bsyms.contains(x) || fixed(x); });
		auto newvar_info = bsyms.insert({newvar,newvar});// the new name should be avoided
		if( newvar == var ) {// the bound variable is fresh
			body = body._map(f,fixed,bsyms);
		} else {
			// replace the original name
			auto replace_info = bsyms.insert({abs->first,newvar});
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
	} else if( auto fix = this->fix() ) {
		Term newbox = subst_var(f,fix->first,bsyms);
		Term newval = fix->second._map(f,fixed,bsyms);
		if( auto nsym = newbox.sym() ) {
			return *nsym / newval;
		} else if( auto nabs = newbox.abs() ) {
			return nabs->second.subst(nabs->first,newval);
		} else {
			throw UnexpectedTerm(newbox);
		}
	} else {
		assert(false);
	}
}

String const VOID_var = String("");
String const IMP_var = String("⟹");
String const ALL_var = String("∀");
Term const IMP = Term(IMP_var);
Term const ALL = Term(ALL_var);

Ctxt::Opt<String const> Ctxt::find_sym_local(String const& sym) const {
	auto const& it = fvars().find(sym);
	if( it != fvars().end() ) {
		return {&*it};
	}
	auto const& spec_it = specs().find(sym);
	if( spec_it != specs().end() ) {
		return {&spec_it->first};
	}
	return {nullptr};
}

Ctxt::Opt<String const> Ctxt::find_sym(String const& sym) const {
	if( auto opt = find_sym_local(sym) ) {
		return opt;
	} else if( auto parent = find_ctxt() ) {
		return parent->find_sym(sym);
	} else {
		return {nullptr};
	}
}

CTerm Ctxt::fix(String const& sym) {
	if( auto opt = find_sym(sym) ) {
		return CTerm(*this,*opt);
	}
	_ref->fvars.insert(sym);
	_ref->fvar_list.push_back(sym);
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
		[&](String const& sym){ if( !find_sym(sym) ) { throw UnboundVariable(sym); } }
	);
	return CTerm(*this,t);
}
Term Ctxt::_thm(String const& name) const {
	auto it = _ref->thms.find(name);
	if( it == _ref->thms.end() ) {
		if( auto parent = find_ctxt() ) {
			return parent->_thm(name);
		}
		throw TheoremNotFound(name);
	}
	return it->second;
}

pair<CTerm,Ctxt const> Ctxt::obtain(String const& sym, std::vector<std::pair<String,Term>> const& specs) {
	if( find_sym(sym) ) {
		throw DoubleFix(sym);
	}
	Ctxt obtainer = branch();
	String thesis = avoid("thesis",[&](String const& x){ return find_sym(x) || sym == x; });
	Term assm = thesis;
	obtainer._ref->specs.insert({sym,specs});// register the specification
	for( auto it = specs.rbegin(); it != specs.rend(); it++ ) {
		obtainer.cterm(it->second);// check closedness
		assm = it->second >>= assm;
		obtainer._ref->thms.insert(*it);
	}
	assm = ALL( thesis /= ALL( sym /= assm ) >>= thesis );
	obtainer._ref->assms.push_back(assm);
	return {CTerm(*this,assm),obtainer};
}
Thm Thm::_allE(CTerm const& t) const {
	auto const& a = app();
	if( a && a->first == ALL ) {
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
	auto const& syms = _ctxt.fvar_list();
	for( auto it = syms.rbegin(); it != syms.rend(); it++ ) {
		stmt = ALL(*it /= stmt);
	}
	return Thm(CTerm(parent,stmt));
}
std::optional<CTerm::StrTerm> CTerm::abs() const {
	if( auto tabs = Term::abs() ) {
		String const& var = tabs->first;
		Term const& body = tabs->second;
		Ctxt loc = _ctxt.branch();
		loc.fix(var);
		return StrTerm(var,CTerm(loc,body));
	} else {
		return nullopt;
	}
}
CTerm CTerm::lift() const {
	auto const& parent = _ctxt.ctxt();
	Term ret = *this;
	for( auto const& sym : _ctxt.fvar_list() ) {
		ret = sym /= ret;
	}
	return CTerm(parent,ret);
}

CTerm CTerm::subst(CSubst const& subst) const {
	auto const& ctxt = subst.ctxt();
	_ctxt.ensure_ancestor(ctxt);
	auto f = [&](String const& sym)->Term {
		if( auto const& opt = subst.get(sym) ) {
			return *opt;
		} else if( auto const& opt2 = ctxt.find_sym(sym) ) {
			return *opt2;
		} else {
			throw UnboundVariable(sym);
		}
	};
	auto fixed = [&](String const& sym)->bool {
		return subst.ctxt().find_sym(sym);
	};
	return CTerm(ctxt,map(f,fixed));
}
Ctxt Ctxt::interpret(CSubst const& subst, std::vector<Thm> const& facts) const {
	auto const& parent = ctxt();
	if( subst.ctxt() != parent ) {
		throw WrongContext();
	}
	Ctxt ret = parent.branch();
	for( auto& fvar : fvars() ) {// fix uninstantiated variables
		if( !subst.map().contains(fvar) ) {
			ret.fix(fvar);
		}
	}
	auto it = facts.begin();
	for( auto const& assm : assms() ) {// check that the instances of assumptions are discharged
		if( it == facts.end() ) {
			throw MalformedDischarge(assm,Term("#context"));
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
	// copy specified constants and theorems
	for( auto const& spec : specs() ) {
		ret._ref->specs.insert(spec);
	}
	for( auto const& thm : thms() ) {
		ret._ref->thms.insert({thm.first,thm.second.subst(subst)});
	}
	return ret;
}
Ctxt& Ctxt::import(Ctxt const& ctxt) {
	if( auto const& parent = ctxt.find_ctxt() ) {
		ensure_ancestor(*parent);
	}
	for( auto& fvar : ctxt.fvar_list() ) {
		_ref->fvars.insert(fvar);
		_ref->fvar_list.push_back(fvar);
	}
	for( auto& spec : ctxt.specs() ) {
		_ref->specs.insert(spec);
	}
	for( auto& assm : ctxt.assms() ) {
		_ref->assms.push_back(assm);
	}
	for( auto& thm : ctxt.thms() ) {
		_ref->thms.insert(thm);
	}
	return *this;
}

