#include"util.hpp"

using namespace std;

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

bool unify0(String const& var, Term const& val, Syms const& fsyms, TermMap& subst) {
	if( fsyms.contains(var) && !var_occurs(var,val) ) {
		subst.insert({var,val});
		return true;
	}
	return false;
}

bool unify1(String const& x, Term const& r, Syms const& fsyms, TermMap& subst) {
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
		auto it = find(fsyms.begin(),fsyms.end(),y);
		if( it != fsyms.end() ) {
			subst.insert({y,x});
			return true;
		}
	}
	return unify0(x,r,fsyms,subst);
}

bool unify2(Ctxt const& ctxt, Term const& l, Term const& r, Syms const& fsyms, TermMap& subst) {
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
		string str = x;
		make_fresh(str,ctxt);// make a fresh variable z
		String z = str;
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

bool unify(Ctxt const& ctxt, Term const& l, Term const& r, Syms const& fsyms, TermMap& subst) {
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
