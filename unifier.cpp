#include"unifier.hpp"

using namespace std;

String make_fresh(Ctxt const& ctxt, String const& orig) {
	string ret = orig;
	while( ctxt.fixes(ret) ) {
		ret.append("'");
	}
	return String(ret);
}
String make_fresh(TermMap const& subst, String const& orig) {
	string ret = orig;
	while( subst.contains(ret) ) {
		ret.append("'");
	}
	return String(ret);
}

/**
 * @brief strips universal quantifiers into context variables
 * @return the stripped theorem in a context with (distinct) fixed variables
 */
Thm strip_all(Ctxt& ctxt, Thm const& t) {
	Thm cur = t.adopt(ctxt);
	for(;;) {
		auto const& x = cur.all();
		if( x.has_value() ) {
			auto const& v = x->first;
			String const& nv = make_fresh(ctxt,v);
			ctxt.fix(nv);
			cur = cur.instantiate(nv);
		} else {
			return cur;
		}
	}
}

bool var_occurs(String const& v, Term const& t) {
	try {
		t.iter_syms(
			[](String const& s){},
			[v](String const& s){ if( s == v ) { throw true; } });
		return false;
	} catch(bool x) {
		return x;
	}
}

bool unify0(String const& var, Term const& val, Syms& fsyms, TermMap& subst) {
	auto it = fsyms.find(var);
	if( it == fsyms.end() || var_occurs(var,val) ) {
		return false;
	}
	fsyms.erase(it);// not free anymore
	subst.insert({var,val});
	return true;
}

bool unify1(String const& x, Term const& r, Syms& fsyms, TermMap& subst) {
	auto const& rsym = r.sym();
	if( rsym.has_value() ) {
		String const& y = *rsym;
		// first, test if y must be substituted. It covers the variable capture.
		if( subst.contains(y) ) {
			return unify1(x,subst[y],fsyms,subst);
		}
		if( x == y ) {
			return true;
		}
		auto it = fsyms.find(y);
		if( it != fsyms.end() ) {
			fsyms.erase(it);
			subst.insert({y,x});
			return true;
		}
	}
	return unify0(x,r,fsyms,subst);
}

bool unify2(Ctxt const& ctxt, Term const& l, Term const& r, Syms& fsyms, TermMap& subst) {
	auto const& rsym = r.sym();
	if( rsym.has_value() ) {
		if( subst.contains(*rsym) ) {
			return unify2(ctxt,l,subst[*rsym],fsyms,subst);
		}
		return unify0(*rsym,l,fsyms,subst);
	}
	auto const& lapp = l.app();
	if( lapp.has_value() ) {
		auto const& rapp = r.app();
		return rapp.has_value() &&
			unify(ctxt,lapp->first,rapp->first,fsyms,subst) &&
			unify(ctxt,lapp->second,rapp->second,fsyms,subst);
	}
	auto const& labs = l.abs();
	if( labs.has_value() ) {
		auto const& rabs = r.abs();
		if( !rabs.has_value() ) {
			return false;
		}
		// both are abstraction.
		String const& x = labs->first;
		String const& y = rabs->first;
		String z = make_fresh(ctxt,x);// make a fresh variable z
		Ctxt ctxt2 = ctxt.branch();
		ctxt2.fix(z);
		return unify(ctxt2,labs->second.subst(x,z),rabs->second.subst(y,z),fsyms,subst);
	}
	auto const& lfix = l.fix();
	assert( lfix.has_value() );
	auto const& fix2 = r.fix();
	if( !fix2.has_value() ) {
		return false;
	}
	return lfix->first == fix2->first && unify(ctxt,lfix->second,fix2->second,fsyms,subst);
}

bool unify(Ctxt const& ctxt, Term const& l, Term const& r, Syms& fsyms, TermMap& subst) {
	auto const& lsym = l.sym();
	if( lsym.has_value() ) {
		String const& x = *lsym;
		if( subst.contains(x) ) {
			return unify(ctxt,subst[x],r,fsyms,subst);
		}
		return unify1(x,r,fsyms,subst);
	}
	return unify2(ctxt,l,r,fsyms,subst);
}

/**
 * @brief Automatically instantiate universally quantified variables so that implication premises are discharged.
 * 
 * @param t 
 * @param args 
 * @return the resulting theorem.
 */
Thm inst_discharge(Thm t, list<Thm> args) {
	Ctxt ctxt = t.ctxt();
	Ctxt loc1 = ctxt.branch();// will contain the free variables
	t = strip_all(loc1,t);
	Term body = t;// stripped body
	Syms fsyms = loc1.syms();
	TermMap subst;
	for( auto& arg : args ) {
		auto const& imp = body.imp();
		if( !imp.has_value() ) {
			throw MalformedDischarge(body,arg);
		}
		// strip the arg in the new context
		arg = strip_all(loc1,arg);
		if( !unify(loc1,imp->first,arg,fsyms,subst) ) {
			throw MalformedDischarge(body,arg);
		}
		body = imp->second;
	}
	// quantifying remaining free variables
	Ctxt loc2 = ctxt.branch();
	for( auto const& fsym : fsyms ) {
		loc2.fix(fsym);
	}
	t = t.lift(ctxt).adopt(loc2);
	for( auto& arg : args ) {
		arg = arg.lift(ctxt).adopt(loc2);
	}
	// instantiate assigned variables
	for( auto const& bvar : loc1.sym_list() ) {
		if( subst.contains(bvar) ) {
			t = t.instantiate(subst[bvar]);
			for( auto& arg : args ) {
				arg = arg.instantiate(subst[bvar]);
			}
		} else {
			loc2.fix(bvar);
			t = t.instantiate(bvar);
			for( auto& arg : args ) {
				arg = arg.instantiate(bvar);
			}
		}
	}
	// discharge conditions
	for( auto const& arg : args ) {
		t = t.discharge(arg);
	}
	return t.lift(ctxt);
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
