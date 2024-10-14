#include"util.hpp"

using namespace std;

class Unifier {
	function<bool(string const&)> const& fvar;// free variables
	CSubst subst;
public:
	struct Mismatch : exception {};
	struct Occurs : exception {};
	struct Escapes : exception {};
	Unifier(Ctxt const& ctxt, function<bool(string const&)> const& fvar) : subst(ctxt), fvar(fvar) {}
private:
	map<string,unsigned int,less<>> escapes[2];
	StrSet avoids[2];

	static Term sanitize(Term const& t, StrSet& bounds, StrSet const& avoids, map<string,unsigned int,less<>> const& escapes) {
		if( auto sym = t.sym() ) {
			string const& x = *sym;
			if( bounds.contains(x) ) {// local bound variable is OK
				return x;
			}
			if( avoids.contains(x) ) {// occurs check
				throw Occurs();
			}
			if( escapes.contains(x) ) {// variable must not escape
				throw Escapes();
			}
			return t;
		} else if( auto app = t.app() ) {
			return sanitize(app->first,bounds,avoids,escapes)(sanitize(app->second,bounds,avoids,escapes));
		} else if( auto abs = t.abs() ) {
			string const& x = abs->first;
			auto const& info = bounds.insert(x);
			auto const& body = sanitize(abs->second,bounds,avoids,escapes);
			if( info.second ) {
				bounds.erase(info.first);
			}
			return x /= body;
		} else if( auto fix = t.fix() ) {
			return fix->first / sanitize(fix->second,bounds,avoids,escapes);
		} else {
			assert(false);
		}
	}

	void unify1(string const& x, Term const& r) {
		if( auto rsym = r.sym() ) {
			string const& y = *rsym;
			if( x == y ) {
				return;
			}
			if( escapes[1].contains(y) ) { // this case is already tested
				throw Mismatch();
			}
			// test if y has an assigned value.
			if( auto const& yval = subst.get(y) ) {
				unify1(x,*yval);
				return;
			}
			if( fvar(y) ) {// free variables can be assigned
				StrSet bounds;
				subst.assign(y,x);
				return;
			}
		}
		throw Mismatch();
	}
	void unify2(Term const& l, Term const& r, unsigned int index) {
		if( auto rsym = r.sym() ) {
			string const& y = *rsym;
			if( escapes[1].contains(y) ) { // bound variable cannot match other things
				throw Mismatch();
			}
			// test if y has an assigned value.
			if( auto const& yval = subst.get(y) ) {
				avoids[0].insert(y);// this rhs cannot be unified with lhs containing y
				unify2(l,*yval,index);
				avoids[0].erase(y);
				return;
			}
			if( fvar(y) ) {// free variables can be assigned
				StrSet bounds;
				subst.assign(y,sanitize(l,bounds,avoids[0],escapes[0]));
				return;
			}
			throw Mismatch();
		} else if( auto lapp = l.app() ) {
			if( auto rapp = r.app() ) {
				unify(lapp->first,rapp->first,index);
				unify(lapp->second,rapp->second,index);
				return;
			} else {
				throw Mismatch();
			}
		} else if( auto labs = l.abs() ) {
			if( auto rabs = r.abs() ) {
				// both are abstraction.
				string const& x = labs->first;
				string const& y = rabs->first;
				auto const& xinfo = escapes[0].insert({x,index});
				auto const& yinfo = escapes[1].insert({y,index});
				unify(labs->second,rabs->second,index+1);
				// forget the bound variables
				if( xinfo.second ) {
					escapes[0].erase(xinfo.first);
				}
				if( yinfo.second ) {
					escapes[1].erase(yinfo.first);
				}
				return;
			} else {
				throw Mismatch();
			}
		} else if( auto lfix = l.fix() ) {
			if( auto rfix = r.fix() ) {
				if( lfix->first == rfix->first ) {
					unify(lfix->second,rfix->second,index);
					return;
				}
			}
			throw Mismatch();
		} else {
			assert(false);
		}
	}
public:
	void unify(Term const& l, Term const& r, unsigned int index = 0) {
		if( auto lsym = l.sym() ) {
			string const& x = *lsym;
			auto const& xesc_it = escapes[0].find(x);
			if( xesc_it != escapes[0].end() ) {// bound variable must have the same index.
				if( auto rsym = r.sym() ) {
					auto const& yesc_it = escapes[1].find(*rsym);
					if( yesc_it != escapes[1].end() ) {
						if( xesc_it->second == yesc_it->second ) {
							return;
						}
					}
				}
				throw Mismatch();
			}
			if( x == r ) {
				return;
			}
			// test if substitution is necessary
			if( auto xval = subst.get(x) ) {
				avoids[1].insert(x);// this lhs cannot be unified with rhs containing x
				unify(*xval,r);
				avoids[1].erase(x);
				return;
			}
			if( fvar(x) ) {// local variables can be assigned
				StrSet bounds;
				subst.assign(x,sanitize(r,bounds,avoids[1],escapes[1]));
				return;
			}
			return unify1(x,r);
		}
		unify2(l,r,index);
	}
	CSubst result() {
		StrSet done;
		for( auto& x : subst.map() ) {
			subst.assign(x.first,subst.get(x.first)->subst(subst));
		}
		return subst;
	}
};

Opt<CSubst> unify(CTerm const& l, CTerm const& r, function<bool(string const&)> const& fvar) {
	if( r.ctxt() != l.ctxt() ) {
		throw WrongContext("unify");
	}
	Unifier u = Unifier(l.ctxt(),fvar);
	try {
		u.unify(l,r);
		return u.result();
	} catch( exception const& e ) {
		return {};
	}
}

Thm discharge(Thm thm, Thm arg) try {
	Ctxt ctxt = thm.ctxt();
	// expand thm into cond ⟹ concl
	Ctxt thm_ctxt = ctxt.branch();
	Thm thm_strip = strip_all(thm,thm_ctxt);
	auto imp = thm_strip.cbinary(IMP);
	if( !imp ) throw 0;
	// expand cond
	CTerm cond = imp->first;
	Ctxt cond_ctxt = thm_ctxt.branch();
	CTerm cond_strip = strip_all(cond,cond_ctxt);
	// expand arg
	Ctxt arg_ctxt = cond_ctxt.branch();
	Thm arg_strip = strip_all(arg,arg_ctxt);
	cond_strip = cond_strip.weaken(arg_ctxt);
	cond = cond.weaken(arg_ctxt);
	Opt<CSubst> unifier = unify(cond_strip,arg_strip,[&](string const& x){
		return thm_ctxt.fvars().contains(x) || arg_ctxt.fvars().contains(x);
	} );
	if( !unifier ) throw 3;
	// unassigned free variables will be universally quantified in the result
	Ctxt ret_ctxt = ctxt.branch();
	iter_local_vars(arg_ctxt,[&](string const& x){
		if( !unifier->map().contains(x) ) {
			ret_ctxt.fix(x);
		}
	});
	iter_local_vars(thm_ctxt,[&](string const& x){
		if( !unifier->map().contains(x) ) {
			ret_ctxt.fix(x);
		}
	});
	// instantiating arg according to the unifier
	// quantify variables as cond
	Ctxt discharger_ctxt = ret_ctxt.branch();
	iter_local_vars(cond_ctxt,[&](string const& x){
		discharger_ctxt.fix(x);
	});
	arg = arg.weaken(discharger_ctxt);
	iter_local_vars(arg_ctxt,[&](string const& x) {// TODO: slower than `subst`
		auto val = unifier->get(x);
		arg = arg.allE( discharger_ctxt.cterm( val ? *val : Term(x) ) );
	});
	arg = arg.intro();
	thm = thm.weaken(ret_ctxt);
	iter_local_vars(thm_ctxt,[&](string const& x) {// TODO: slower than `subst`
		auto val = unifier->get(x);
		thm = thm.allE( ret_ctxt.cterm( val ? *val : Term(x) ) );
	});
	thm = thm.impE(arg);
	thm = thm.intro();
	return thm;
} catch( int n ) {
	throw MalformedDischarge(thm,arg);
}
