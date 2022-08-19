#include"util.hpp"

using namespace std;

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

Thm allI(Thm const& thm, String const& var) {
	Ctxt ctxt = thm.ctxt();
	return thm.weaken(ctxt.branch().fix(var)).lift(ctxt);
}

bool match(Ctxt const& loc, Term const& pat, Term const& val, TermMap& matcher) {
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

void make_fresh(string& str, Ctxt const& ctxt) {
	while( ctxt.fixes(str) ) {
		str.append("'");
	}
}

void strip_all(Thm& thm, Ctxt& ctxt) {
	for(;;) {
		auto const& all = thm.all();
		if( all.has_value() ) {
			string str = all->first;
			make_fresh(str,ctxt);
			String nv = String(str);
			ctxt.fix(nv);
			thm = thm.allE(nv);
		} else {
			return;
		}
	}
}
void strip_all(Term& t, Ctxt& ctxt) {
	for(;;) {
		auto const& all = t.all();
		if( all.has_value() ) {
			String const& v = all->first;
			string str = v;
			make_fresh(str,ctxt);
			String nv = String(str);
			ctxt.fix(nv);
			t = all->second.subst(v,nv);
		} else {
			return;
		}
	}
}

Thm discharge(Thm thm, Thm arg) {
	Ctxt ctxt = thm.ctxt();
	Ctxt loc = ctxt.branch();
	strip_all(thm,loc);
	auto const& imp = thm.imp();
	if( !imp.has_value() ) {
		throw MalformedDischarge(thm,arg);
	}
	TermMap subst;
	if( !match(loc,imp->first,arg,subst) ) {
		throw MalformedDischarge(thm,arg);
	}
	for( auto const& p : subst ) {
		thm = allI(thm,p.first).allE(p.second);
	}
	thm = thm.impE(arg);
	// quantify remaining free variables
	for( auto const& fsym : loc.sym_list() ) {
		if( !subst.contains(fsym) ) {
			thm = allI(thm,fsym);
		}
	}
	return thm;
}

