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

bool match(Ctxt const& loc, Term const& pat, Term const& val, StrMap<Term>& matcher) {
	auto const& sym = pat.sym();
	if( sym.has_value() ) {
		String const& x = *sym;
		if( matcher.contains(x) ) {// already assigned variable
			return matcher[x] == val;
		}
		if( loc.syms().contains(x) ) {// free symbol
			matcher.insert({*sym,val});// assigning to the variable
			return true;
		}
		return pat == val;
	}
	auto const& app = pat.app();
	if( app.has_value() ) {
		auto const& app2 = val.app();
		return app2.has_value() &&
			match(loc,app->first,app2->first,matcher) &&
			match(loc,app->second,app2->second,matcher);
	}
	auto const& abs = pat.abs();
	if( abs.has_value() ) {
		auto const& abs2 = val.abs();
		if( !abs2.has_value() ) {
			return false;
		}
		String const& x = abs->first;
		String const& y = abs2->first;
		auto it = matcher.find(x);
		if( it != matcher.end() ) {
			Term pre = it->second;//remember old assignment
			it->second = y;// replace the assignment to y
			if( match(loc,abs->second,abs2->second,matcher) ) {
				it->second = pre;// recover the old assignment
				return true;
			}
			return false;
		}
		matcher.insert({x,y});// assign x := y
		if( match(loc,abs->second,abs2->second,matcher) ) {
			matcher.erase(x);// forget the assignment
			return true;
		}
		return false;
	}
	auto const& fix = pat.fix();
	assert( fix.has_value() );
	auto const& fix2 = val.fix();
	if( !fix2.has_value() ) {
		return false;
	}
	return fix->first == fix2->first && match(loc,fix->second,fix2->second,matcher);
}


Thm strip_all(Thm thm, Ctxt& ctxt) {
	thm = thm.weaken(ctxt);
	for(;;) {
		auto const& app = thm.app();
		if( app.has_value() && app->first == ALL ) {
			auto const& abs = app->second.abs();
			if( abs.has_value() ) {
				String const& v = abs->first;
				String nv = avoid(v,[&](String const& x){ return ctxt.find(x).has_value(); });
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
				String nv = avoid(v,[&](String const& x){ return ctxt.find(x).has_value(); });
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
	arg = arg.lift(ret_ctxt);
	thm = thm.weaken(ret_ctxt);
	for( auto const& x : thm_ctxt.sym_list() ) {// TODO: slower than `subst`
		auto opt = unifier->get(x);
		auto const& val = opt.has_value() ? (Term)*opt : x;
		thm = thm.allE(ret_ctxt.cterm(val));
	}
	thm = thm.impE(arg);
	thm = thm.lift(ctxt);
	return thm;
}

