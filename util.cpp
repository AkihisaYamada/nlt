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
		auto const& all = thm.all();
		if( all.has_value() ) {
			String const& v = all->first;
			String nv = avoid(v,[&](String const& x){ return ctxt.find(x).has_value(); });
			thm = thm.allE(ctxt.fix(nv));
		} else {
			return thm;
		}
	}
}
CTerm strip_all(CTerm t, Ctxt& ctxt) {
	t = t.weaken(ctxt);
	for(;;) {
		auto const& app = t.app();
		if( app.has_value() && app->first == ALL ) {
			auto const& abs = app->first.abs();
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
	Ctxt loc = ctxt.branch();
	// computing unifier
	thm = strip_all(thm,loc);
	auto const& imp = thm.imp();
	if( !imp.has_value() ) {
		throw MalformedDischarge(thm,arg);
	}
	arg = strip_all(arg,loc);
	CTerm cond = imp->first;
	optional<CSubst> unifier = unify(cond,arg);
	if( !unifier.has_value() ) {
		throw MalformedDischarge(thm,arg);
	}
	// instantiating according to the unifier
	Ctxt loc2 = ctxt.branch();
	thm = thm.lift(ctxt).weaken(loc2);
	arg = arg.lift(ctxt).weaken(loc2);
cerr << thm << endl << arg << endl;
	for( auto const& x : loc.sym_list() ) {// TODO: slower than `subst`
		auto opt = unifier->get(x);
		auto const& val = opt.has_value() ? opt->lift(ctxt).weaken(loc2) : loc2.fix(x);
		thm = thm.allE(val);
		arg = arg.allE(val);
	}
	thm = thm.impE(arg);
	thm = thm.lift(ctxt);
	return thm;
}

