#include<list>
#include<algorithm>
#include"core.hpp"

using namespace std;

String avoid_vars(String const& orig, set<String>& avoids) {
	string ret = orig;
	while( avoids.contains(ret) ) {
		ret.append("'");
	}
	return String(ret);
}

/**
 * @brief strips universal quantifiers
 * 
 * @param t 
 * @param fvs 
 * @return a pair of the stripped term and the list of (distinct) free variables
 */
pair<Term,list<String>> strip_all(Term const& t, set<String>& fvs) {
	Term cur = t;
	list<String> vars;
	for(;;) {
		auto const& x = cur.all();
		if( x.has_value() ) {
			auto const& v = x->first;
			if( fvs.contains(v) ) {
				String const& nv = avoid_vars(v,fvs);
				vars.push_back(nv);
				fvs.insert(nv);
				cur = x->second.subst(v,nv);
			} else {
				vars.push_back(v);
				cur = x->second;
			}
		} else {
			return pair<Term,list<String>>(cur,vars);
		}
	}
}

pair<list<Term>,Term> explode_imp(Term const& t) {
	list<Term> ret;
	Term const* cur = &t;
	for(;;) {
		auto const& imp = cur->imp();
		if( imp.has_value() ) {
			ret.push_back(imp->first);
			cur = &imp->second;
		} else {
			return pair(ret,*cur);
		}
	}
}

/**
 * @brief Matching, assuming disjoint free variables.
 * 
 * @param vars the list of free variables in pattern
 * @param pat 
 * @param val 
 */
bool match(list<String> const& vars, Term const& pat, Term const& val, TermMap& subst, VarMaker vm) {
	auto const& sym = pat.sym();
	if( sym.has_value() ) {
		if( subst.contains(*sym) ) {// the variable is already fixed
			return subst[*sym] == val;
		}
		auto const& it = find(vars.begin(),vars.end(),*sym);
		if( it == vars.end() ) {// pat is non-free symbol
			return pat == val;
		}
		// fixing the free variable
		subst.insert({*it,val});
		return true;
	}
	auto const& app = pat.app();
	if( app.has_value() ) {
		auto const& app2 = val.app();
		return app2.has_value() &&
			match(vars,app->first,app2->first,subst,vm) &&
			match(vars,app->second,app2->second,subst,vm);
	}
	auto const& abs = pat.abs();
	if( abs.has_value() ) {
		auto const& abs2 = val.abs();
		if( !abs2.has_value() ) {
			return false;
		}
		String nv = vm.make();
		return match(vars,abs->second.subst(abs->first,nv),abs2->second.subst(abs2->first,nv),subst,vm);
	}
	return false;
}

Thm inst_discharge(set<String> fvars, Thm const& t, list<Thm> const& args) {
	auto const& p = strip_all(t,fvars);
	list<String> bvars = p.second;
	TermMap subst;
	Term const* body = &p.first;
	for( auto const& arg : args ) {
		auto const& imp = body->imp();
		if( !imp.has_value() || !match(bvars,imp->first,arg,subst,VarMaker()) ) {
			throw MalformedDischarge(*body,arg);
		}
		body = &imp->second;
	}
	// to quantify unfixed variables
	Ctxt ctxt = t.ctxt().branch();
	for( auto const& bvar : bvars ) {
		if( !subst.contains(bvar) ) {
			ctxt.fix(bvar);
		}
	}
	// instantiate fixed variables
	Thm tmp = t.adopt(ctxt);
	for( auto const& bvar : bvars ) {
		if( subst.contains(bvar) ) {
			tmp = tmp.instantiate(subst[bvar]);
		} else {
			tmp = tmp.instantiate(bvar);
		}
	}
	// discharge conditions
	for( auto const& arg : args ) {
		tmp = tmp.discharge(arg);
	}
	return tmp.lift(t.ctxt());
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
