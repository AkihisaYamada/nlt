#include"util.hpp"

using namespace std;

pair<string, list<Term>> uncurry(Term const& t) {
	Term const* cur = &t;
	list<Term> args;
	for(;;) {
		if( auto const& app = cur->app() ) {
			args.push_front(app->second);
			cur = &app->first;
		} else if( auto sym = cur->sym() ) {
			return pair<string,list<Term>>(*sym,args);
		} else {
			throw Error(*cur);
		}
	}
}

static bool match(StrSet const& fsyms, CTerm const& pat, CTerm const& val, CSubst& matcher, StrMap<unsigned int>& lidx, StrMap<unsigned int>& ridx, unsigned int depth) {
	if( auto sym = pat.sym() ) {
		if( auto lidx_it = lidx.find(*sym); lidx_it != lidx.end() ) {// bound variable must be identical
			if( auto rsym = val.sym() ) {
				auto ridx_it = ridx.find(*rsym);
				return ridx_it != ridx.end() && lidx_it->second == ridx_it->second;
			} else {
				return false;
			}
		} else if( auto const& map_opt = matcher.get(*sym) ) {// already assigned variable
			return (Term)*map_opt == val;// equal as term (may belong to different context)
		} else if( fsyms.contains(*sym) ) {// free symbol
			matcher.assign(*sym,val);// assigning to the variable
			return true;
		} else {
			return *sym == val;
		}
	} else if( auto app = pat.capp() ) {
		if( auto app2 = val.capp() ) {
			return match(fsyms,app->first,app2->first,matcher,lidx,ridx,depth) &&
				match(fsyms,app->second,app2->second,matcher,lidx,ridx,depth);
		} else {
			return false;
		}
	} else if( auto const& abs = pat.cabs() ) {
		if( auto const& abs2 = val.cabs() ) {
			string const& x = abs->first;
			string const& y = abs2->first;
			depth++;
			auto const& lidx_info = lidx.insert({x,depth});
			auto const& ridx_info = ridx.insert({y,depth});
			unsigned int lpre;
			unsigned int rpre;
			if( !lidx_info.second ) {
				lpre = lidx_info.first->second;// remember the old index
				lidx_info.first->second = depth;// and update
			}
			if( !ridx_info.second ) {
				rpre = ridx_info.first->second;// remember the old index
				ridx_info.first->second = depth;// and update
			}
			if( match(fsyms,abs->second,abs2->second,matcher,lidx,ridx,depth) ) {
				// recover the old indices
				if( lidx_info.second ) {
					lidx.erase(lidx_info.first);
				} else {
					lidx_info.first->second = lpre;
				}
				if( ridx_info.second ) {
					ridx.erase(ridx_info.first);
				} else {
					ridx_info.first->second = rpre;
				}
				return true;
			}
			return false;
		} else {
			return false;
		}
	} else if( auto fix = pat.cfix() ) {
		auto [x,_,b] = *fix;
		if( auto const& opt = matcher.get(x) ) {
			if( auto const& abs = opt->abs() ) {
				return match(fsyms,opt->inst(b),val,matcher,lidx,ridx,depth);
			}
		}
		if( auto fix2 = val.cfix() ) {
			auto [_,x2,b2] = *fix2;
			if( fsyms.contains(x) ) {
				matcher.assign(x,x2);
			}
			return match(fsyms,b,b2,matcher,lidx,ridx,depth);
		} else {
			return false;
		}
	} else {
		assert(false);
	}
}

Opt<CSubst> match(StrSet const& fsyms, CTerm const& pat, CTerm const& val) {
	CSubst ret = val.ctxt();
	StrMap<unsigned int> lidx, ridx;
	if( match(fsyms,pat,val,ret,lidx,ridx,0) ) {
		return ret;
	}
	return {};
}
Term strip_all(Term t, Ctxt& ctxt) {
	while( auto all = t.binder(ALL) ) {
		auto [v,b] = *all;
		string nv = avoid(v,[&](string const& x){ return ctxt.fixed(x); });
		t = b.subst(v,ctxt.fix(nv));
	}
	return t;
}
Thm strip_all(Thm thm, Ctxt& ctxt) {
	thm = thm.weaken(ctxt);
	while( auto all = thm.binder(ALL) ) {
		auto [v,b] = *all;
		string nv = avoid(v,[&](string const& x){ return ctxt.fixed(x); });
		thm = thm.allE(ctxt.fix(nv));
	}
	return thm;
}
CTerm strip_all(CTerm t, Ctxt& ctxt) {
	t = t.weaken(ctxt);
	while( auto all = t.binder(ALL) ) {
		auto [v,b] = *all;
		string nv = avoid(v,[&](string const& x){ return ctxt.fixed(x); });
		auto nvt = ctxt.fix(nv);
		t = b.csubst(CSubst(ctxt).assign(v,nvt));
	}
	return t;
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


Thm Concluder::conclude(Thm const& thm) {
	auto const& app1 = thm.capp();
	assert(app1);
	auto const& app2 = app1->first.capp();
	assert(app2);
	CTerm const& source = app2->second; // thm = source ⟹ ...
	for( Rule const& rule : rules ) {
		auto const& pat_ctxt = rule.pat.ctxt();
		if( auto const& m = match(pat_ctxt.fvars(),rule.pat,source) ) {
			Thm arg = rule.thm.weaken(source.ctxt());
			iter_local_vars(pat_ctxt,[&](string const& fvar){
				arg = arg.allE(*m->get(fvar));
			});
			return thm.impE(arg);
		}
	}
	throw Error(thm);
}

