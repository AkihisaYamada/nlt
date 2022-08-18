#include"matcher.hpp"

using namespace std;

String make_fresh(Ctxt const& ctxt, String const& orig) {
	string ret = orig;
	while( ctxt.fixes(ret) ) {
		ret.append("'");
	}
	return String(ret);
}

/**
 * @brief strips universal quantifiers
 * @return the stripped theorem in a context with (distinct) fixed variables
 */
Thm strip_all(Thm const& t) {
	Ctxt ctxt = t.ctxt().branch();
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

/**
 * @brief Matching, assuming disjoint free variables.
 * 
 * @param ctxt context which fixes non variable symbols.
 * @param pat 
 * @param val 
 */
bool match(Ctxt const& ctxt, Term const& pat, Term const& val, TermMap& subst, VarMaker vm) {
	auto const& sym = pat.sym();
	if( sym.has_value() ) {
		if( ctxt.fixes(*sym) ) {// fixed symbol
			return pat == val;
		}
		if( subst.contains(*sym) ) {// already assigned variable
			return subst[*sym] == val;
		}
		// assigning the free variable
		subst.insert({*sym,val});
		return true;
	}
	auto const& app = pat.app();
	if( app.has_value() ) {
		auto const& app2 = val.app();
		return app2.has_value() &&
			match(ctxt,app->first,app2->first,subst,vm) &&
			match(ctxt,app->second,app2->second,subst,vm);
	}
	auto const& abs = pat.abs();
	if( abs.has_value() ) {
		auto const& abs2 = val.abs();
		if( !abs2.has_value() ) {
			return false;
		}
		String nv = vm.make();
		return match(ctxt,abs->second.subst(abs->first,nv),abs2->second.subst(abs2->first,nv),subst,vm);
	}
	auto const& fix = pat.fix();
	assert( fix.has_value() );
	auto const& fix2 = val.fix();
	if( !fix2.has_value() ) {
		return false;
	}
	return fix->first == fix2->first && match(ctxt,fix->second,fix2->second,subst,vm);
}
/**
 * @brief Automatically instantiate universally quantified variables so that implication premises are discharged.
 * 
 * @param t 
 * @param args 
 * @return the resulting theorem.
 */
Thm inst_discharge(Thm const& t, list<Thm> const& args) {
	Ctxt ctxt = t.ctxt();
	Thm const& t2 = strip_all(t);
	Term const* body = &t2;
	Ctxt const& loc1 = t2.ctxt();
	TermMap subst;
	for( auto const& arg : args ) {
		auto const& imp = body->imp();
		if( !imp.has_value() || !match(ctxt,imp->first,arg,subst,VarMaker()) ) {
			throw MalformedDischarge(*body,arg);
		}
		body = &imp->second;
	}
	// instantiate assigned variables
	Ctxt loc2 = ctxt.branch();
	Thm tmp = t.adopt(loc2);
	for( auto const& bvar : loc1.sym_list() ) {
		if( subst.contains(bvar) ) {
			tmp = tmp.instantiate(subst[bvar]);
		} else {
			loc2.fix(bvar);
			tmp = tmp.instantiate(bvar);
		}
	}
	// discharge conditions
	for( auto const& arg : args ) {
		tmp = tmp.discharge(arg.adopt(loc2));
	}
	return tmp.lift(ctxt);
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
