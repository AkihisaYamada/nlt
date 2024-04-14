#include<cstring>
#include"core.hpp"

using namespace std;

string avoid(string const& var, function<bool(string const&)> const& test) {
	if( !test(var) ) {
		return var;
	}
	string str = var;
	do {
		str.push_back('\'');
	} while( test(str) );
	return str;
}

static bool _eq_var(string const& x, string const& y, StrMap<unsigned int>& lmap, StrMap<unsigned int>& rmap ) {
	auto lopt = lmap.finds(x);
	auto ropt = rmap.finds(y);
	if( lopt ) {
		return ropt && *lopt == *ropt;
	}
	return !ropt && x == y;
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
			auto const& linfo = lmap.emplace(labs->first,depth);
			unsigned int lprev;
			if( linfo.second ) {
				lprev = 0;
			} else {
				lprev = linfo.first->second;
				linfo.first->second = depth;
			}
			auto const& rinfo = rmap.emplace(rabs->first,depth);
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
	function<void(string const&)> const& bsym,
	function<void(string const&)> const& fsym
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

CSubst& CSubst::_assign(string const& var, CTerm const& val) {
	auto const& info = _map.emplace(var,val);
	if( !info.second ) {
		info.first->second = val;
	}
	return *this;
}

Term Term::subst(CSubst const& subst) const {
	if( subst.empty() ) {
		return *this;
	}
	auto f = [&](string const& sym)->Term {
		if( auto opt = subst.get(sym) ) {
			return *opt;
		} else {
			return sym;
		}
	};
	auto fixed = [&](string const& sym) {
		return (bool)subst.ctxt().find_sym(sym);
	};
	return map(f,fixed);
}

static Term subst_var(function<Term(string const&)> f, string const& sym, StrMap<string>& bsyms) {
	if( auto opt = bsyms.finds(sym) ) {
		return opt->second;
	}
	return f(sym);
}

Term Term::_map(function<Term(string const&)> f, function<bool(string const&)> fixed, StrMap<string>& bsyms) const {
	if( auto sym = this->sym() ) {
		return subst_var(f,*sym,bsyms);
	} else if( auto app = this->app() ) {
		return app->first._map(f,fixed,bsyms)(app->second._map(f,fixed,bsyms));
	} else if( auto abs = this->abs() ) {
		string var = abs->first;
		Term body = abs->second;
		string const& newvar = avoid(var,[&](string const& x){ return bsyms.contains(x) || fixed(x); });
		auto newvar_info = bsyms.emplace(newvar,newvar);// the new name should be avoided
		if( newvar == var ) {// the bound variable is fresh
			body = body._map(f,fixed,bsyms);
		} else {
			// replace the original name
			auto replace_info = bsyms.emplace(abs->first,newvar);
			string prev;
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

string const IMP_var = "⟹";
string const ALL_var = "∀";
Term const IMP = Term(IMP_var);
Term const ALL = Term(ALL_var);

Opt<string const&> Ctxt::find_sym(string const& sym) const & {
	if( auto opt = find_fvar(sym) ) {
		return *opt;
	}
	if( auto opt = find_constant(sym) ) {
		return opt->first;
	}
	if( auto parent = find_parent() ) {
		return parent->find_sym(sym);
	}
	return {};
}

Ctxt Ctxt::branch(
	std::vector<std::string>&& fvar_list,
	std::vector<std::pair<std::string,Term>> const& assms
) const {
	StrSet fvars;
	for( string const& fvar : fvar_list ) {
		fvars.insert(fvar);
	}
	for( auto const& [name,assm] : assms ) {
		assm.iter_fsyms(
			[this,&fvars](string const& sym){
				if( !find_sym(sym) && fvars.contains(sym) ) {
					throw UnboundVariable(sym);
				}
			}
		);
	}
	StrMap<Ctxt const> ctxts;
	ctxts.emplace("",*this);
	return Ctxt(Ref<Body>::make(
		std::move(ctxts),std::move(fvars),std::move(fvar_list),Specs()
	));
}

CTerm Ctxt::cterm(Term const& t) const {
	t.iter_fsyms(
		[&](string const& sym){ if( !find_sym(sym) ) { throw UnboundVariable(sym); } }
	);
	return CTerm(*this,t);
}

pair<CTerm,Ctxt const> Ctxt::obtain(
	string const& sym,
	Specs const& specs
) {
	if( find_sym(sym) ) {
		throw DoubleFix(sym);
	}
	string thesis = avoid("thesis", [&](string const& x){ return find_sym(x) || sym == x; });
	Term assm = thesis;
	vector<Term> thms;
	for( auto it = specs.rbegin(); it != specs.rend(); it++ ) {
		auto const& thm = it->second;
		// check closedness
		thm.iter_fsyms(
			[&](string const& x){ if( !find_sym(x) && x != sym ) { throw UnboundVariable(x); } }
		);
		assm = thm >>= assm;
		thms.push_back(thm);
	}
	assm = ALL( thesis /= ALL( sym /= assm ) >>= thesis );
	StrMap<Ctxt const> ctxts;
	ctxts.emplace("",*this);
	StrSet fvars = {sym};
	vector<string> fvar_list = {sym};
	vector<Term> assms = {assm};
	Ctxt obtainer = Ctxt(Ref<Body>::make(
		std::move(fvars),
		std::move(fvar_list),
		std::move(assms),
		std::move(specs),
		std::move(thms)
	));
	return {CTerm(*this,assm),obtainer};
}
Thm Thm::_allE(CTerm const& t) const {
	if( auto const& a = app() ) {
		if( a->first == ALL ) {
			return a->second.inst(t);
		}
	}
	throw MalformedInstantiation(*this,t);
}

Thm Thm::impE(Thm const& t) const {
	if( t.ctxt() != ctxt() ) {
		throw WrongContext();
	}
	if( auto const& app1 = app() ) {
		if( auto const& app2 = app1->first.app() ) {
			if( app2->first == IMP && app2->second == t ) {
				return app1->second;
			}
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
Opt<CTerm::StrTerm> CTerm::abs() const {
	if( auto tabs = Term::abs() ) {
		string const& var = tabs->first;
		Term const& body = tabs->second;
		Ctxt loc = _ctxt.branch({var},{});
		return StrTerm(var,CTerm(loc,body));
	} else {
		return {};
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
	auto fixed = [&](string const& sym) {
		return (bool)subst.ctxt().find_sym(sym);
	};
	if( subst.empty() ) {
		// only check that the term is closed.
		return ctxt.cterm(*this);
	}
	auto f = [&](string const& sym)->Term {
		if( auto const& opt = subst.get(sym) ) {
			return *opt;
		} else if( auto const& opt2 = ctxt.find_sym(sym) ) {
			return *opt2;
		} else {
			throw UnboundVariable(sym);
		}
	};
	return CTerm(ctxt,map(f,fixed));
}
Intp::Intp(Ctxt const& ctxt, CSubst&& subst, std::vector<Thm> const& thms) :
	_ctxt(ctxt), _subst(std::move(subst)) {
	for( auto& fvar : _ctxt.fvars() ) {// check that all variables are fixed
		if( !_subst.closes(fvar) ) {
			throw UnboundVariable(fvar);
		}
	}
	auto const& owner = _subst.ctxt();
	owner.ensure_ancestor(_ctxt.ctxt());// the interpreted context must belong to an ancestor of the owner
	auto it = thms.begin();
	for( auto const& assm : _ctxt.assms() ) {// check that the instances of assumptions are discharged
		if( it == thms.end() ) {
			throw MalformedDischarge(assm,Term("#context"));
		}
		if( it->ctxt() != owner ) {
			throw WrongContext();
		}
		Term const& goal = assm.subst(_subst);
		if( *it != goal ) {
			throw MalformedDischarge(goal,*it);
		}
		it++;
	}
}


