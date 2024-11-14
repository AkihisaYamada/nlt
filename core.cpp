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
		return ropt && lopt->second == ropt->second;
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
	function<void(string_view const&)> const& bsym,
	function<void(string_view const&)> const& fsym
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

CSubst& CSubst::_assign(string_view const& var, Term const& val) {
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
	auto f = [&](string_view const& sym)->Term {
		if( auto opt = subst.get(sym) ) {
			return *opt;
		} else {
			return sym;
		}
	};
	auto fixed = [&](string_view const& sym)->Opt<Term> {
		if( auto t = subst.ctxt().constant(sym) ) {
			return *t;
		}
		return {};
	};
	return map(f,fixed);
}

static function<Term(string_view const&)> unit_map(string_view const& var, Term const& val) {
	return [&](auto sym){ return sym == var ? val : Term(sym); };
}
Term Term::subst(string_view const& var, CTerm const& val) const {
	return map(
		unit_map(var,val),
		[&](auto sym)->Opt<Term>{
			if( auto t = val.ctxt().constant(sym) ) {
				return *t;
			}
			return {};
		}
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
	function<Term(string_view const&)> f,
	function<bool(string_view const&)> fixed,
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

inline Term Term::inst(CTerm const& arg) const {
	auto a = abs();
	if( !a ) {
		throw MalformedInstantiation(*this,arg);
	}
	return a->second.subst(a->first,arg);
}

string const IMP = "⟹";
string const ALL = "∀";

Ctxt::Ctxt() : Ctxt(Ref<Body>::make()) {
	_ref->fvars.insert(IMP);
	_ref->fvars.insert(ALL);
}

bool Ctxt::has_constant(string_view const& sym) const {
	if( fixes(sym) || obtains(sym) ) {
		return true;
	}
	if( auto parent = find_parent() ) {
		return parent->constant(sym);
	}
	return false;
}
CTerm Ctxt::cterm(Term const& t) const {
	t.iter_syms( [&](auto sym){
		if( !constant(sym) ) {
			throw UnboundVariable(sym);
		}
	} );
	return CTerm(*this,t);
}
Opt<CTerm> Ctxt::closed(Term const& t) const {
	try {
		return cterm(t);
	} catch( UnboundVariable const& e ) {
		return {};
	}
}
CTerm Ctxt::enclose(Term const& t) {
	t.iter_syms( [&](auto sym){
		if( !constant(sym) ) {
			fix(sym);
		}
	} );
	return CTerm(*this,t);
}

CTerm Ctxt::fix(string_view const& s) & {
	if( fixes(s)) {
		throw DoubleFix(s);
	}
	_ref->modifiers.push_back(_Fix(s));
	_ref->fvars.emplace(s);
	return CTerm(*this,s);
}

Thm Ctxt::_assume(Term const& t) & {
	_ref->modifiers.push_back(_Assume(t));
	return CTerm(*this,t);
}

Thm Ctxt::assume(CTerm const& t) & {
	if( t.ctxt() != *this ) {
		throw WrongContext("assume");
	}
	return _assume(t);
}

pair<CTerm,Thm> Ctxt::obtain(string_view const& sym, Thm const& thm) & {
	if( constant(sym) ) {
		throw DoubleFix(sym);
	}
	// thm should be ∀thesis. (∀sym'. props... ⟹ thesis) ⟹ thesis
	auto all1 = thm.binder(ALL);
	if( !all1 ) {
		throw MalformedObtain(thm);
	}
	auto thesis = all1->first;
	auto imp = all1->second.binary(IMP);
	if( !imp || imp->second != thesis ) {
		throw MalformedObtain(thm);
	}
	auto all2 = imp->first.unary(ALL);
	if( !all2 ) {
		throw MalformedObtain(thm);
	}
	auto abs = all2->abs();
	if( !abs ) {
		throw MalformedObtain(thm);
	}
	auto sym2 = abs->first;
	Term t = abs->second;// props... ⟹ thesis
	// check that props do not contain thesis
	Term const* in = &t;
	while( auto imp2 = in->binary(IMP) ) {
		auto& prop = imp2->first;
		prop.iter_syms(
			[&](auto str){ if( str == thesis ) throw MalformedObtain(prop); }
		);
		in = &imp2->second;
	}
	if( *in != thesis ) {
		throw MalformedObtain(thm);
	}
	// (props[var:=sym]... ⟹ thesis) ⟹ thesis
	_ref->constants.emplace(sym);
	_ref->modifiers.push_back(_Obtain(string(sym),thm));
	auto sym_term = CTerm(*this,sym);
	Thm spec = CTerm( *this, thesis &= all2->inst(sym_term) >>= thesis );
	return {sym_term,spec};
}
Thm Thm::_allE(CTerm const& t) const {
	if( auto const& a = cunary(ALL) ) {
		return a->inst(t);
	}
	throw MalformedInstantiation(*this,t);
}

Thm Thm::impE(Thm const& t) const {
	if( t.ctxt() != ctxt() ) {
		throw WrongContext("impE");
	}
	if( auto const& imp = cbinary(IMP) ) {
		if( imp->first == t ) {
			return imp->second;
		}
	}
	throw MalformedDischarge(*this)(t);
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
	for( size_t i = _ctxt.revision(); i > 0; ) {
		i--;
		if( auto const& assm = _ctxt.assumed(i) ) {
			stmt = *assm >>= stmt;
		} else if( auto const& fix = _ctxt.fixed(i) ) {
			stmt = *fix &= stmt;
		} else if( auto const& obtain = _ctxt.obtained(i) ) {
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
CTerm CTerm::lift( CTerm const& quantifier ) const {
	auto const& parent = _ctxt.ctxt();
	if( quantifier.ctxt() != parent ) {
		throw WrongContext("lift");
	}
	Term ret = *this;
	for( size_t i = _ctxt.revision(); i > 0; ) {
		i--;
		if( auto fix = _ctxt.fixed(i) ) {
			ret = ((Term)quantifier)( *fix /= ret );
		}
	}
	return CTerm(parent,ret);
}

CTerm Term::csubst(CSubst const& subst) const {
	auto const& ctxt = subst.ctxt();
	auto fixed = [&](string_view const& sym)->Opt<Term> {
		if( auto t = subst.ctxt().constant(sym) ) {
			return *t;
		}
		return {};
	};
	if( subst.empty() ) {
		// only check that the term is closed.
		return ctxt.cterm(*this);
	}
	auto f = [&](string_view const& sym)->Term {
		if( auto const& opt = subst.get(sym) ) {
			return *opt;
		} else if( ctxt.constant(sym) ) {
			return sym;
		} else {
			throw UnboundVariable(sym);
		}
	};
	return CTerm(ctxt,map(f,fixed));
}
Intp Intp::make(Ctxt const& src, Ctxt const& tgt) {
	if( auto srcParent = src.find_parent() ) {
		if( !tgt.has_ancestor(*srcParent) ) {
			throw WrongContext("making interpretation");
		}
	}
	return Intp(src,tgt);
}
CTerm Intp::subst(CTerm const& thm) const {
	if( thm.ctxt() != _src ) {
		throw WrongContext("interpretation");
	}
	if( _src.revision() != _rev ) {
		throw WrongContext("wrong revision");
	}
	return CTerm(_subst.ctxt(),thm.subst(_subst));
}
void Intp::instantiate(CTerm const& term) {
	auto fix = _src.fixed(_rev);
	if( !fix ) {
		throw WrongContext("unexpected instantiate");
	}
	_subst.assign(*fix,term);
	_rev++;
}
void Intp::discharge(Thm const& thm) {
	auto assume = _src.assumed(_rev);
	if( !assume ) {
		throw UnexpectedTerm("discharge");
	}
	Term const& exp = assume->subst(_subst);
	if( exp != thm ) {
		throw MalformedDischarge(exp)(thm);
	}
	_rev++;
}
void Intp::retain(CTerm const& term, Thm const& thm) {
	if( thm.ctxt() != _subst.ctxt() ) {
		throw WrongContext("retain");
	}
	auto obtain = _src.obtained(_rev);
	if( !obtain ) {
		throw UnexpectedTerm("retain");
	}
	string const& sym = obtain->first;
	Term t = obtain->second.subst(_subst);// ∀thesis. (∀sym. specs... ⟹ thesis) ⟹ thesis
	auto all = t.binder(ALL);
	assert( all );
	auto thesis = all->first;
	t = all->second; // (∀sym. specs... ⟹ thesis) ⟹ thesis
	auto imp = t.binary(IMP);
	assert( imp );
	t = imp->first; // ∀sym. specs... ⟹ thesis, thesis
	auto abs = t.unary(ALL);
	assert( abs );
	t = abs->inst(term); // specs[sym:=term]... ⟹ thesis
	t = thesis &= t >>= thesis; // ∀thesis. (specs[sym:=term]... ⟹ thesis) ⟹ thesis
	if( thm != t ) {
		throw MalformedRetain(thm);
	}
	_subst.assign(sym,term);
	_rev++;
}

