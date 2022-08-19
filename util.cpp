#include"util.hpp"

using namespace std;

Thm allI(Thm const& thm, String const& var) {
	Ctxt ctxt = thm.ctxt();
	return thm.weaken(ctxt.branch().fix(var)).lift(ctxt);
}

String make_fresh(list<String> const& syms, Ctxt const& ctxt, String const& orig) {
	string ret = orig;
	while( ctxt.fixes(ret) ) {
		ret.append("'");
	}
	while( find(syms.begin(),syms.end(),ret) != syms.end() ) {
		ret.append("'");
	}
	return String(ret);
}

Thm strip_all(list<String>& fsyms, Thm t) {
	Ctxt const& ctxt = t.ctxt();
	for(;;) {
		auto const& all = t.all();
		if( all.has_value() ) {
			auto const& v = all->first;
			String const& nv = make_fresh(fsyms,ctxt,v);
			fsyms.push_back(nv);
			t = t.allE(nv);
		} else {
			return t;
		}
	}
}
Term strip_all(list<String>& fsyms, Ctxt const& ctxt, Term const& t) {
	Term cur = t;
	for(;;) {
		auto const& all = cur.all();
		if( all.has_value() ) {
			auto const& v = all->first;
			String const& nv = make_fresh(fsyms,ctxt,v);
			ctxt.fix(nv);
			cur = all->second.subst(v,nv);
		} else {
			return cur;
		}
	}
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

bool match(list<String> const& fsyms, Term const& pat, Term const& val, TermMap& matcher) {
	auto const& sym = pat.sym();
	if( sym.has_value() ) {
		String const& x = *sym;
		if( matcher.contains(x) ) {// already assigned variable
			return matcher[x] == val;
		}
		auto it = find(fsyms.begin(),fsyms.end(),*sym);
		if( it == fsyms.end() ) {// fixed symbol
			return pat == val;
		}
		matcher.insert({*sym,val});// assigning to the variable
		return true;
	}
	auto const& app = pat.app();
	if( app.has_value() ) {
		auto const& app2 = val.app();
		return app2.has_value() &&
			match(fsyms,app->first,app2->first,matcher) &&
			match(fsyms,app->second,app2->second,matcher);
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
			if( match(fsyms,abs->second,abs2->second,matcher) ) {
				it->second = pre;// recover the old assignment
				return true;
			}
			return false;
		}
		matcher.insert({x,y});// assign x := y
		if( match(fsyms,abs->second,abs2->second,matcher) ) {
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
	return fix->first == fix2->first && match(fsyms,fix->second,fix2->second,matcher);
}

Thm inst_discharge(Thm thm, list<Thm> args) {
	Ctxt ctxt = thm.ctxt();
	list<String> fsyms;
	thm = strip_all(fsyms,thm);
	for( auto const& arg : args ) {
		auto const& imp = thm.imp();
		if( !imp.has_value() ) {
			throw MalformedDischarge(thm,arg);
		}
		TermMap matcher;
		if( !match(fsyms,imp->first,arg,matcher) ) {
			throw MalformedDischarge(thm,arg);
		}
		for( auto const& p : matcher ) {
			thm = allI(thm,p.first).allE(p.second);
			fsyms.erase(find(fsyms.begin(),fsyms.end(),p.first));// not free anymore
		}
		thm = thm.impE(arg);
	}
	// quantify free variables again
	for( auto const& fsym : fsyms ) {
		thm = allI(thm,fsym);
	}
	return thm;
}

