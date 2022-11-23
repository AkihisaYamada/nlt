#include"util.hpp"

using namespace std;

ostream& operator<<(ostream& os, Term const& t) {
	auto const& sym = t.sym();
	if( sym.has_value() ) {
		return os << *sym;
	}
	auto const& app = t.app();
	if( app.has_value() ) {
		return os << '(' << app->first << ' ' << app->second << ')';
	}
	auto const& abs = t.abs();
	if( abs.has_value() ) {
		return os << abs->first << ". " << abs->second;
	}
	auto const& fix = t.fix();
	assert( fix.has_value() );
	return os << fix->first << ".[" << fix->second << ']';
}
ostream& operator<<(ostream& os, CSubst const& subst) {
	char const* punct = "[ ";
	for( auto const& x : subst.map() ) {
		os << punct << x.first << " := " << x.second;
		punct = ",\n  ";
	}
	return os << "\n]";
}

pair<Term const&, list<Term>> uncurry(Term const& t) {
	Term const* cur = &t;
	list<Term> args;
	for(;;) {
		auto const& p = cur->app();
		if( p.has_value() ) {
			args.push_front(p->second);
			cur = &p->first;
		} else {
			return pair<Term const&, list<Term>>(*cur,args);
		}
	}
}

static bool match(Syms const& fsyms, CTerm const& pat, CTerm const& val, CSubst& matcher, StrMap<unsigned int>& lidx, StrMap<unsigned int>& ridx, unsigned int depth) {
	auto const& sym = pat.sym();
	if( sym.has_value() ) {
		String const& x = *sym;
		auto lidx_it = lidx.find(x);// bound variable must be identical
		if( lidx_it != lidx.end() ) {
			auto const& rsym = val.sym();
			if( !rsym.has_value() ) {
				return false;
			}
			auto const& ridx_it = ridx.find(*rsym);
			if( ridx_it == ridx.end() || lidx_it->second != ridx_it->second ) {
				return false;
			}
			return true;
		}
		auto const& map_opt = matcher.get(x);
		if( map_opt.has_value() ) {// already assigned variable
			if( (Term)*map_opt != val ) {// equal as term (may belong to different context)
				return false;
			}
			return true;
		}
		if( fsyms.contains(x) ) {// free symbol
			matcher.assign(*sym,val);// assigning to the variable
			return true;
		}
		if( x == val ) {
			return true;
		}
		return false;
	}
	auto const& app = pat.app();
	if( app.has_value() ) {
		auto const& app2 = val.app();
		if( !app2.has_value() ) {
			return false;
		}
		return match(fsyms,app->first,app2->first,matcher,lidx,ridx,depth) &&
			match(fsyms,app->second,app2->second,matcher,lidx,ridx,depth);
	}
	auto const& abs = pat.abs();
	if( abs.has_value() ) {
		auto const& abs2 = val.abs();
		if( !abs2.has_value() ) {
			return false;
		}
		String const& x = abs->first;
		String const& y = abs2->first;
		depth++;
		auto const& lidx_info = lidx.insert({x,depth});
		auto const& ridx_info = ridx.insert({y,depth});
		unsigned int lpre;
		unsigned int rpre;
		if( !lidx_info.second ) {
			lpre = lidx_info.first->second;// remember the old index
			lidx_info.first->second = depth;// and update
		}
		if( !ridx_info.second ) {
			rpre = ridx_info.first->second;// remember the old index
			ridx_info.first->second = depth;// and update
		}
		if( match(fsyms,abs->second,abs2->second,matcher,lidx,ridx,depth) ) {
			// recover the old indices
			if( lidx_info.second ) {
				lidx.erase(lidx_info.first);
			} else {
				lidx_info.first->second = lpre;
			}
			if( ridx_info.second ) {
				ridx.erase(ridx_info.first);
			} else {
				ridx_info.first->second = rpre;
			}
			return true;
		}
		return false;
	}
	auto const& fix = pat.fix();
	assert( fix.has_value() );
	auto const& x = fix->first;
	auto const& opt = matcher.get(x);
	if( opt.has_value() ) {
		auto const& abs = opt->abs();
		if( abs.has_value() ) {
			return match(fsyms,opt->inst(fix->second),val,matcher,lidx,ridx,depth);
		}
	}
	auto const& fix2 = val.fix();
	if( !fix2.has_value() ) {
		return false;
	}
	if( fsyms.contains(x) ) {
		matcher.assign(x,fix2->first);
	}
	return match(fsyms,fix->second,fix2->second,matcher,lidx,ridx,depth);
}

optional<CSubst> match(Syms const& fsyms, CTerm const& pat, CTerm const& val) {
	CSubst ret = val.ctxt();
	StrMap<unsigned int> lidx, ridx;
	if( match(fsyms,pat,val,ret,lidx,ridx,0) ) {
		return ret;
	}
	return optional<CSubst>();
}

Thm strip_all(Thm thm, Ctxt& ctxt) {
	thm = thm.weaken(ctxt);
	for(;;) {
		auto const& app = thm.app();
		if( app.has_value() && app->first == ALL ) {
			auto const& abs = app->second.abs();
			if( abs.has_value() ) {
				String const& v = abs->first;
				String nv = avoid(v,[&](String const& x){ return ctxt.find_sym(x).has_value(); });
				thm = thm.allE(ctxt.fix(nv));
				continue;
			}
		}
		return thm;
	}
}
CTerm strip_all(CTerm t, Ctxt& ctxt) {
	t = t.weaken(ctxt);
	for(;;) {
		auto const& app = t.app();
		if( app.has_value() && app->first == ALL ) {
			auto const& abs = app->second.abs();
			if( abs.has_value() ) {
				String const& v = abs->first;
				String nv = avoid(v,[&](String const& x){ return ctxt.find_sym(x).has_value(); });
				t = app->second.inst(ctxt.fix(nv));
				continue;
			}
		}
		return t;
	}
}

Thm discharge(Thm thm, Thm arg) {
	Ctxt ctxt = thm.ctxt();
	// expand thm into cond ⟹ concl
	Ctxt thm_ctxt = ctxt.branch();
	Thm thm_strip = strip_all(thm,thm_ctxt);
	auto const& app1 = thm_strip.app();
	if( !app1.has_value() ) {
		throw MalformedDischarge(thm,arg);
	}
	auto const& app2 = app1->first.app();
	if( !app2.has_value() || app2->first != IMP ) {
		throw MalformedDischarge(thm,arg);
	}
	// expand cond
	CTerm cond = app2->second;
	Ctxt cond_ctxt = thm_ctxt.branch();
	CTerm cond_strip = strip_all(cond,cond_ctxt);
	// expand arg
	Ctxt arg_ctxt = cond_ctxt.branch();
	Thm arg_strip = strip_all(arg,arg_ctxt);
	cond_strip = cond_strip.weaken(arg_ctxt);
	cond = cond.weaken(arg_ctxt);
	optional<CSubst> unifier = unify(cond_strip,arg_strip,[&](String const& x){
		return thm_ctxt.syms().contains(x) || arg_ctxt.syms().contains(x);
	} );
	if( !unifier.has_value() ) {
		throw MalformedDischarge(thm,arg);
	}
	// unassigned free variables will be universally quantified in the result
	Ctxt ret_ctxt = ctxt.branch();
	for( auto const& x : arg_ctxt.sym_list() ) {
		if( !unifier->map().contains(x) ) {
			ret_ctxt.fix(x);
		}
	}
	for( auto const& x : thm_ctxt.sym_list() ) {
		if( !unifier->map().contains(x) ) {
			ret_ctxt.fix(x);
		}
	}
	// instantiating arg according to the unifier
	// quantify variables as cond
	Ctxt discharger_ctxt = ret_ctxt.branch();
	for( auto const& x : cond_ctxt.sym_list() ) {
		discharger_ctxt.fix(x);
	}
	arg = arg.weaken(discharger_ctxt);
	for( auto const& x : arg_ctxt.sym_list() ) {// TODO: slower than `subst`
		auto opt = unifier->get(x);
		auto const& val = opt.has_value() ? (Term)*opt : x;
		arg = arg.allE(discharger_ctxt.cterm(val));
	}
	arg = arg.intro();
	thm = thm.weaken(ret_ctxt);
	for( auto const& x : thm_ctxt.sym_list() ) {// TODO: slower than `subst`
		auto opt = unifier->get(x);
		auto const& val = opt.has_value() ? (Term)*opt : x;
		thm = thm.allE(ret_ctxt.enclose(val));
	}
	thm = thm.impE(arg);
	thm = thm.intro();
	return thm;
}

