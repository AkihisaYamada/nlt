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
	StrMSet& bsyms,
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
		auto it = bsyms.insert(abs->first);
		abs->second._iter_syms(bsyms,bsym,fsym);
		bsyms.erase(it);
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
		return subst.ctxt().fixed(sym);
	};
	return map(f,fixed);
}

static function<Term(string const&)> unit_map(string const& var, Term const& val) {
	return [&](std::string const& sym){ return sym == var ? val : Term(sym); };
}
Term Term::subst(string const& var, CTerm const& val) const {
	return map(
		unit_map(var,val),
		[&](std::string const& sym){ return val.ctxt().fixed(sym); }
	);
}

static Term subst_var(
	function<Term(string const&)> f,
	string const& sym,
	StrMap<string>& bsyms
) {
	if( auto opt = bsyms.finds(sym) ) {
		return opt->second;
	}
	return f(sym);
}

Term Term::_map(
	function<Term(string const&)> f,
	function<bool(string const&)> fixed,
	StrMap<string>& bsyms
) const {
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
			return nabs->second.map(unit_map(nabs->first,newval));
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

Ctxt::Ctxt() : Ctxt(Ref<Body>::make()) {
	_ref->fvars.insert(IMP_var);
	_ref->fvars.insert(ALL_var);
}

bool Ctxt::fixed(string const& sym) const & {
	if( fixes(sym) ) {
		return true;
	}
	if( specifies(sym) ) {
		return true;
	}
	if( auto parent = find_parent() ) {
		return parent->fixed(sym);
	}
	return false;
}

CTerm Ctxt::cterm(Term const& t) const {
	t.iter_fsyms(
		[&](string const& sym){ if( !fixed(sym) ) { throw UnboundVariable(sym); } }
	);
	return CTerm(*this,t);
}

CTerm Ctxt::fix(string const& s) & {
	if( fixes(s)) {
		throw DoubleFix(s);
	}
	_ref->modifiers.push_back(Fix(s));
	_ref->fvars.insert(s);
	return CTerm(*this,s);
}

Thm Ctxt::_assume(Term const& t) & {
	_ref->modifiers.push_back(Assume(t));
	return CTerm(*this,t);
}

Thm Ctxt::assume(Term const& t) & {
	cterm(t);
	return _assume(t);
}

Thm Ctxt::assume(CTerm const& t) & {
	if( t.ctxt() != *this ) {
		throw WrongContext("assume");
	}
	return _assume(t);
}

vector<Thm> Ctxt::obtain(Thm const& thm) & {
	// thm should be ∀thesis. (∀sym. spec_1 ⟹ ... ⟹ spec_n ⟹ thesis) ⟹ thesis
	auto all1 = thm.binder(ALL);
	if( !all1 ) {
		throw UnexpectedTerm(thm);
	}
	auto thesis = all1->first;
	auto imp = all1->second.binary(IMP);
	if( !imp || imp->second != thesis ) {
		throw UnexpectedTerm(thm);
	}
	auto all2 = imp->first.binder(ALL);
	if( !all2 ) {
		throw UnexpectedTerm(thm);
	}
	auto sym = all2->first;
	if( fixed(sym) ) {
		throw DoubleFix(sym);
	}
	vector<Term> props;
	vector<Thm> thms;
	Term const* in = &all2->second;
	while( auto imp2 = in->binary(IMP) ) {
		auto& prop = imp2->first;
		prop.iter_fsyms(// spec should not contain thesis
			[&](auto str){ if( str == thesis ) throw UnexpectedTerm(prop); }
		);
		props.push_back(prop);
		thms.push_back(CTerm(*this,prop));
		in = &imp2->second;
	}
	if( *in != thesis ) {
		throw UnexpectedTerm(thm);
	}
	_ref->modifiers.push_back(Obtain(sym,std::move(props)));
	_ref->constants.insert(sym);
	return thms;
}
Thm Thm::_allE(CTerm const& t) const {
	if( auto const& a = capp() ) {
		if( a->first == ALL ) {
			return a->second.inst(t);
		}
	}
	throw MalformedInstantiation(*this,t);
}

Thm Thm::impE(Thm const& t) const {
	if( t.ctxt() != ctxt() ) {
		throw WrongContext("impE");
	}
	if( auto const& app1 = capp() ) {
		if( auto const& app2 = app1->first.app() ) {
			if( app2->first == IMP && app2->second == t ) {
				return app1->second;
			}
		}
	}
	throw MalformedDischarge(*this,t);
}

Thm Thm::intro() const {
	if( !_ctxt.consts().empty() ) {// checks if obtained constants don't escape
		auto check = [&](auto v){
			if( _ctxt.consts().contains(v) ) { throw ConstantEscape(v); }
		};
		iter_fsyms(check);
	}
	auto const& parent = _ctxt.ctxt();
	Term stmt = *this;
	auto const& modifiers = _ctxt.modifiers();
	for( auto it = modifiers.rbegin(); it != modifiers.rend(); it++ ) {
		if( auto const& assm = it->ref<Ctxt::Assume>() ) {
			stmt = *assm >>= stmt;
		} else if( auto const& fix = it->ref<Ctxt::Fix>() ) {
			stmt = ALL( *fix /= stmt );
		} else if( auto const& obtain = it->ref<Ctxt::Obtain>() ) {
			// obtain is safe
		} else {
			assert(false);
		}
	}
	return Thm(CTerm(parent,stmt));
}
Opt<CTerm::StrTerm> CTerm::cabs() const {
	if( auto tabs = Term::abs() ) {
		string const& var = tabs->first;
		Term const& body = tabs->second;
		Ctxt loc = _ctxt.branch();
		loc.fix(var);
		return StrTerm(var,CTerm(loc,body));
	} else {
		return {};
	}
}
CTerm CTerm::lift() const {
	auto const& parent = _ctxt.ctxt();
	Term ret = *this;
	for( auto const& mod : _ctxt.modifiers() ) {
		if( auto fix = mod.ref<Ctxt::Fix>() ) {
			ret = *fix /= ret;
		}
	}
	return CTerm(parent,ret);
}

CTerm Term::csubst(CSubst const& subst) const {
	auto const& ctxt = subst.ctxt();
	auto fixed = [&](string const& sym) {
		return subst.ctxt().fixed(sym);
	};
	if( subst.empty() ) {
		// only check that the term is closed.
		return ctxt.cterm(*this);
	}
	auto f = [&](string const& sym)->Term {
		if( auto const& opt = subst.get(sym) ) {
			return *opt;
		} else if( ctxt.fixed(sym) ) {
			return sym;
		} else {
			throw UnboundVariable(sym);
		}
	};
	return CTerm(ctxt,map(f,fixed));
}
Intp Intp::make(Ctxt const& src, Ctxt const& tgt) {
	if( auto tgtParent = tgt.find_parent() ) {
		if( tgtParent != src.find_parent() ) {
			throw WrongContext("making interpretation");
		}
	}
	return Intp(src,tgt);
}
Thm Intp::subst(Thm const& thm) const {
	if( thm.ctxt() != _src ) {
		throw WrongContext("interpretation");
	}
	if( _src.revision() != _rev ) {
		throw WrongContext("wrong revision");
	}
	return Thm(CTerm(_subst.ctxt(),thm.subst(_subst)));
}
void Intp::import_fix(CTerm const& term) {
	if( _src.revision() <= _rev ) {
		throw WrongContext("no need for import_fix");
	}
	auto fix = _src.modifiers()[_rev].ref<Ctxt::Fix>();
	if( !fix ) {
		throw WrongContext("unexpected import_fix");
	}
	_subst.assign(*fix,term);
	_rev++;
}
void Intp::import_assume(Thm const& thm) {
	if( _src.revision() <= _rev ) {
		throw WrongContext("no need for import_assume");
	}
	auto assume = _src.modifiers()[_rev].ref<Ctxt::Assume>();
	if( !assume ) {
		throw WrongContext("unexpected import_assume");
	}
	Term const& exp = assume->subst(_subst);
	if( exp != thm ) {
		throw UnexpectedTerm(Term("#expected")(exp)(thm));
	}
	_rev++;
}
void Intp::import_obtain(CTerm const& term, vector<Thm> const& thms) {
	if( _src.revision() <= _rev ) {
		throw WrongContext("no need for import_obtain");
	}
	auto obtain = _src.modifiers()[_rev].ref<Ctxt::Obtain>();
	if( !obtain ) {
		throw WrongContext("unexpected import_obtain");
	}
	auto& specs = obtain->props();
	auto spec_it = specs.begin();
	auto thm_it = thms.begin();
	for(;;) {
		if( spec_it == specs.end() ) {
			if( thm_it == thms.end() ) {
				_rev++;
				return;
			}
			throw UnexpectedTerm(Term("#too_many_specs")(*thm_it));
		}
		Term spec = spec_it->subst(_subst);
		if( thm_it == thms.end() ) {
			throw MissingProof(spec);
		}
		if( *thm_it != spec ) {
			throw UnexpectedTerm(Term("#expected")(spec)(*thm_it));
		}
		spec_it++;
		thm_it++;
	}
}

