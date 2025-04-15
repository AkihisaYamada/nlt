#include"util.hpp"

using namespace std;

class Unifier {
	function<bool(string const&)> const& fvar;// free variables
	Subst subst;
public:
	struct Mismatch : exception {};
	struct Occurs : exception {};
	struct Escapes : exception {};
	Unifier(Ctxt const& ctxt, function<bool(string const&)> const& fvar) : subst(ctxt), fvar(fvar) {}
private:
	/** stack of bound variables */
	vector<string> bvars[2];
	/** index of bound variables */
	StrMap<unsigned int> inds[2];
	StrSet avoids[2];
	unsigned int index = 0;

	static Term sanitize(Term const& t, StrSet& bounds, StrSet const& avoids, StrMap<unsigned int> const& escapes) {
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
		} else if( auto abs = t.bind() ) {
			string const& x = abs->first;
			auto const& info = bounds.insert(x);
			auto const& body = sanitize(abs->second,bounds,avoids,escapes);
			if( info.second ) {
				bounds.erase(info.first);
			}
			return x /= body;
		} else if( auto fix = t.unbind() ) {
			return fix->first %= sanitize(fix->second,bounds,avoids,escapes);
		} else {
			assert(false);
		}
	}

	// lhs is a symbol
	void unify_lsym(string const& x, CTerm const& r) {
		if( auto const& xesc = inds[0].finds(x) ) {// bound variable must have the same index.
			if( auto rsym = r.sym() )
			if( xesc == inds[1].finds(*rsym) ) {
				return;
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
		if( fvar(x) ) {// free variables can be assigned
			StrSet bounds;
			subst.assign(x,sanitize(r,bounds,avoids[1],inds[1]));
			return;
		}
		return unify_lsym2(x,r);
	}
	// lhs is a constant
	void unify_lsym2(string const& x, Term const& r) {
		if( auto rsym = r.sym() ) {
			string const& y = *rsym;
			if( x == y ) {
				return;
			}
			if( inds[1].contains(y) ) { // this case is already tested
				throw Mismatch();
			}
			if( auto const& yval = subst.get(y) ) {// recurse into the assignment
				unify_lsym2(x,*yval);
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
	// lhs is not a symbol
	void unify_lnsym( CTerm const& l, CTerm const& r ) {
		if( auto rsym = r.sym() ) {
			return unify_rsym(l,*rsym);
		}
		if( auto lunbind = l.cunbind() ) {
			auto const& [x,_,larg] = *lunbind;
			return unify_lunbind(x,larg,r);
		}
		if( auto runbind = r.cunbind() ) {
			auto const& [y,_,rarg] = *runbind;
			return unify_runbind(l,y,rarg);
		}
		return unify2(l,r);
	}
	// when lhs is not but rhs is a symbol
	void unify_rsym(CTerm const& l, string const& y) {
		if( auto rind = inds[1].finds(y) ) { // bound variable cannot match other things
			if( auto lunbind = l.unbind() )// lhs can be higher order pattern
			if( fvar(lunbind->first) )
			if( auto argsym = lunbind->second.sym() )
			if( auto const& lind = inds[0].finds(*argsym) )
			if( rind->second == lind->second ) {
				StrSet bounds;
				subst.assign(lunbind->first,"_"/=Term("_"));
				return;
			}
			throw Mismatch();
		}
		if( auto const& yval = subst.get(y) ) {// recurse into the assignment
			avoids[0].insert(y);// this rhs cannot be unified with lhs containing y
			unify_lnsym(l,*yval);
			avoids[0].erase(y);
			return;
		}
		if( fvar(y) ) {// free variables can be assigned
			StrSet bounds;
			subst.assign(y,sanitize(l,bounds,avoids[0],inds[0]));
			return;
		}
		throw Mismatch();
	}
	// lhs is not symbol or unbinding, rhs is unbinding
	void unify_runbind( CTerm const& l, string const& y, CTerm const& rarg ) {
		if( auto const& val = subst.get(y) ) {// substitution is necessary
			if( auto vsym = val->sym() ) {
				avoids[0].insert(y);// this rhs cannot be unified with lhs containing y
				unify_runbind(l,*vsym,rarg);
				avoids[0].erase(y);
				return;
			} else if( auto vabs = val->cbind() ) {
				avoids[0].insert(y);// this ths cannot be unified with lhs containing y
				unify2(l,val->inst(rarg));
				avoids[0].erase(y);
				return;
			}
		}
		if( fvar(y) )
		if( auto argsym = rarg.sym() )
		if( auto const& opt = inds[1].finds(*argsym) ) {// higher-order pattern
			auto const& [z,i] = *opt;
			StrSet bounds;
			subst.assign(y,sanitize(bvars[0][i]/=l,bounds,avoids[0],inds[0]));
			return;
		}
		throw Mismatch();
	}
	// both sides are application or binding
	void unify2(CTerm const& l, CTerm const& r) {
		if( auto lapp = l.capp() ) {
			if( auto rapp = r.capp() ) {
				unify(lapp->first,rapp->first);
				unify(lapp->second,rapp->second);
				return;
			}
			throw Mismatch();
		} else if( auto lbind = l.cbind() ) {
			auto const& [x,lbody] = *lbind;
			if( auto rbind = r.cbind() ) {
				// both are binding.
				auto const& [y,rbody] = *rbind;
				bvars[0].push_back(x);
				bvars[1].push_back(y);
				auto const& xinfo = inds[0].insert({x,index});
				auto const& yinfo = inds[1].insert({y,index});
				index++;
				unify(lbody,rbody);
				index--;
				// forget the bound variables
				bvars[0].pop_back();
				bvars[1].pop_back();
				if( xinfo.second ) {
					inds[0].erase(xinfo.first);
				}
				if( yinfo.second ) {
					inds[1].erase(yinfo.first);
				}
				return;
			}
			throw Mismatch();
		} else {
			assert(false);
		}
	}
	bool eq_syms( string const& x, string const& y ) {
		if( auto const& xesc = inds[0].finds(x) ) {// bound variable must have the same index.
			return xesc == inds[1].finds(y);
		}
		return x == y;
	}
	// lhs is an unbinding and rhs is not a symbol
	void unify_lunbind( string const& x, CTerm const& larg, CTerm const& r ) {
		if( auto xval = subst.get(x) ) {// context must be substituted
			avoids[1].insert(x);// this lhs cannot be unified with rhs containing x
			if( auto vsym = xval->sym() ) {
				unify_lunbind(*vsym,larg,r);
			} else if( auto vabs = xval->cbind() ) {
				unify(xval->inst(larg),r);
			} else {
				throw Mismatch();
			}
			avoids[1].erase(x);
			return;
		}
		// if rhs is has same context variable, then the arguments are unified
		if( auto const& runbind = r.cunbind() ) {
			auto const& [y,_,rarg] = *runbind;
			if( eq_syms(x,y) ) {
				return unify(larg,rarg);
			}
		}
		// if lhs is a higher-order pattern, then assign the rhs
		if( fvar(x) )
		if( auto argsym = larg.sym() )
		if( auto const& opt = inds[0].finds(*argsym) ) {
			auto const& [z,i] = *opt;
			StrSet bounds;
			subst.assign(x,sanitize(bvars[1][i]/=r,bounds,avoids[1],inds[1]));
			return;
		}
		return unify_lunbind2(x,larg,r);
	}
	// lhs is non-pattern unbinding
	void unify_lunbind2( string const& x, CTerm const& larg, CTerm const& r ) {
		if( auto const& rsym = r.sym() ) {
			return unify_rsym(x/larg,*rsym);
		} if( auto const& rfix = r.cunbind() ) {/// rhs is also a context application
			auto const& [y,_,rarg] = *rfix;
			return unify_fixes(x,larg,y,rarg);
		}
		throw Mismatch();
	}
	// lhs is a non-pattern context and rhs is a context
	void unify_fixes( string const& x, CTerm const& larg, string const& y, CTerm const& rarg ) {
		if( auto val = subst.get(y) ) {// right context has assignment
			avoids[0].insert(y);// this rhs cannot be unified with lhs containing y
			if( auto vsym = val->sym() ) {
				unify_fixes(x,larg,*vsym,rarg);
			} else if( auto vabs = val->cbind() ) {
				unify_lunbind2(x,larg,val->inst(rarg));
			} else {
				throw Mismatch();
			}
			avoids[0].erase(y);
			return;
		}
		if( fvar(y) )
		if( auto argsym = rarg.sym() )
		if( auto const& opt = inds[1].finds(*argsym) ) {// context pattern
			auto const& [z,i] = *opt;
			StrSet bounds;
			subst.assign(y,sanitize(bvars[0][i]/=x/larg,bounds,avoids[0],inds[0]));
			return;
		}
		unify_syms(x,y);
		return unify(larg,rarg);
	}
	void unify_syms( string const& x, string const& y ) {
		if( eq_syms(x,y) ) {
			return;
		}
		if( fvar(x) ) {// free variables can be assigned
			if( avoids[1].contains(y) ) {
				throw Occurs();
			}
			if( inds[1].contains(y) ) {
				throw Escapes();
			}
			subst.assign(x,y);
			return;
		}
		if( fvar(y) ) {
			if( avoids[0].contains(x) ) {
				throw Occurs();
			}
			if( inds[0].contains(x) ) {
				throw Escapes();
			}
			subst.assign(y,x);
			return;
		}
		throw Mismatch();
	}
public:
	void unify(CTerm const& l, CTerm const& r) {
		if( auto lsym = l.sym() ) {
			return unify_lsym(*lsym,r);
		}
		return unify_lnsym(l,r);
	}
	Subst result() {
		StrSet done;
		for( auto& x : subst.map() ) {
			subst.assign(x.first,subst.get(x.first)->subst(subst));
		}
		return subst;
	}
};

Opt<Subst> unify(CTerm const& l, CTerm const& r, function<bool(string const&)> const& fvar) {
	if( r.ctxt() != l.ctxt() ) {
		throw Error("#unify")("\"wrong context\"");
	}
	Unifier u = Unifier(l.ctxt(),fvar);
	try {
		u.unify(l,r);
		return u.result();
	} catch( exception const& e ) {
		return {};
	}
}

Thm discharge(Thm thm, Thm arg) {
	Ctxt ctxt = thm.ctxt();
	// expand thm into cond ⟹ concl
	Ctxt thm_ctxt = ctxt.branch();
	Thm thm_strip = strip_all(thm,thm_ctxt).first;
	auto imp = thm_strip.cbinary(IMP);
	if( !imp ) throw Error("#util")("\"discharge\"")(thm_strip)(arg);
	// expand cond
	CTerm cond = imp->first;
	Ctxt cond_ctxt = thm_ctxt.branch();
	CTerm cond_strip = strip_all(cond,cond_ctxt);
	// expand arg
	Ctxt arg_ctxt = cond_ctxt.branch();
	Thm arg_strip = strip_all(arg,arg_ctxt).first;
	cond_strip = cond_strip.weaken(arg_ctxt);
	cond = cond.weaken(arg_ctxt);
	Opt<Subst> unifier = unify(cond_strip,arg_strip,[&](string const& x){
		return thm_ctxt.fixes(x) || arg_ctxt.fixes(x);
	} );
	if( !unifier ) throw Error("#discharge")(thm)(cond_strip)(arg)(arg_strip);
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
		arg = arg.instantiate( discharger_ctxt.cterm( val ? *val : Term(x) ) );
	});
	arg = arg.intro();
	thm = thm.weaken(ret_ctxt);
	iter_local_vars(thm_ctxt,[&](string const& x) {// TODO: slower than `subst`
		auto val = unifier->get(x);
		thm = thm.instantiate( ret_ctxt.cterm( val ? *val : Term(x) ) );
	});
	thm = thm.discharge(arg);
	thm = thm.intro();
	return thm;
}
