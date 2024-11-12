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

static bool match(StrSet const& fsyms, CTerm const& pat, CTerm const& val, CSubst& matcher, StrMap<unsigned int>& linds, StrMap<unsigned int>& rinds, unsigned int depth) {
	if( auto sym = pat.sym() ) {// pat is a symbol
		if( auto lind = linds.finds(*sym) ) {// pat is a bound variable
			if( auto rsym = val.sym() ) {// val must be a bound variable of the same index
				return rinds.finds(*rsym) == lind;
			}
			return false;
		} else if( auto const& map_opt = matcher.get(*sym) ) {// already assigned variable
			return (Term)*map_opt == val;// equal as term (may belong to different context)
		} else if( fsyms.contains(*sym) ) {// free symbol
			if( val.ctxt() == matcher.ctxt() ) {
				matcher.assign(*sym,val);// assigning to the variable
				return true;
			}
			if( auto cval = matcher.ctxt().closed(val) ) {
				matcher.assign(*sym,*cval);
				return true;
			}
			return false;
		} else {
			return *sym == val;
		}
	} else if( auto app = pat.capp() ) {
		if( auto app2 = val.capp() ) {
			return match(fsyms,app->first,app2->first,matcher,linds,rinds,depth) &&
				match(fsyms,app->second,app2->second,matcher,linds,rinds,depth);
		} else {
			return false;
		}
	} else if( auto const& abs = pat.cabs() ) {
		if( auto const& abs2 = val.cabs() ) {
			string const& x = abs->first;
			string const& y = abs2->first;
			depth++;
			auto const& lind_info = linds.insert({x,depth});
			auto const& rind_info = rinds.insert({y,depth});
			unsigned int lpre;
			unsigned int rpre;
			if( !lind_info.second ) {// the variable was bound twice
				lpre = lind_info.first->second;// remember the old index
				lind_info.first->second = depth;// and update
			}
			if( !rind_info.second ) {
				rpre = rind_info.first->second;// remember the old index
				rind_info.first->second = depth;// and update
			}
			if( match(fsyms,abs->second,abs2->second,matcher,linds,rinds,depth) ) {
				// recover the old indices
				if( lind_info.second ) {
					linds.erase(lind_info.first);
				} else {
					lind_info.first->second = lpre;
				}
				if( rind_info.second ) {
					rinds.erase(rind_info.first);
				} else {
					rind_info.first->second = rpre;
				}
				return true;
			}
			return false;
		} else {
			return false;
		}
	} else if( auto fix = pat.cfix() ) {// x[s]
		auto [x,_,s] = *fix;
		auto const& opt = matcher.get(x);
		if( opt ) if( auto const& abs = opt->abs() ) {// the context is instantiated
			return match(fsyms,opt->inst(s),val,matcher,linds,rinds,depth);
		}
		if( auto fix2 = val.cfix() ) {
			auto [x2,_,s2] = *fix2;
			if( opt ) {// if x is assigned, then it must be x2
				auto const& sym = opt->sym();
				if( !sym || *sym != x2 ) {
					return false;
				}
			}
			if( fsyms.contains(x) ) {// free variable
				if( rinds.finds(x2) ) {// cannot be assigned bound variable
					return false;
				}
				matcher.assign(x,x2);
			} else if( x != x2 ) {// constant
				return false;
			}
			return match(fsyms,s,s2,matcher,linds,rinds,depth);
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
		string nv = avoid(v,[&](string const& x){ return ctxt.constant(x); });
		t = b.subst(v,ctxt.fix(nv));
	}
	return t;
}
Thm strip_all(Thm thm, Ctxt& ctxt) {
	thm = thm.weaken(ctxt);
	while( auto all = thm.binder(ALL) ) {
		auto [v,b] = *all;
		string nv = avoid(v,[&](string const& x){ return ctxt.constant(x); });
		thm = thm.allE(ctxt.fix(nv));
	}
	return thm;
}
CTerm strip_all(CTerm t, Ctxt& ctxt) {
	t = t.weaken(ctxt);
	while( auto all = t.binder(ALL) ) {
		auto [v,b] = *all;
		string nv = avoid(v,[&](string const& x){ return ctxt.constant(x); });
		auto nvt = ctxt.fix(nv);
		t = b.csubst(CSubst(ctxt).assign(v,nvt));
	}
	return t;
}
Thm make_rule( Thm const& thm ) {
	Ctxt loc = thm.ctxt().branch();
	Thm rule = strip_all(thm,loc);
	while( auto imp = rule.cbinary(IMP) ) {
		rule = rule.impE(loc.assume(imp->first));
	}
	return rule;
}
Opt<Thm> rule_applies( Thm const& rule, Thm const& thesis ) {
	Ctxt ctxt = thesis.ctxt().branch();
	Thm tmp = thesis.weaken(ctxt);
	auto imp = tmp.cbinary(IMP);
	if( !imp ) {
		throw Error(Term{"#apply"}(rule)(thesis));
	}
	auto const& m = match(rule.ctxt().fvars(),rule,imp->first);
	if( !m ) {
		return {};
	}
	Intp intp = Intp::make(rule.ctxt(),ctxt);
	for(;;) {
		if( auto v = intp.fixing() ) {
			if( auto val = m->get(*v) ) {
				intp.instantiate(*val);
			} else {
				intp.instantiate(tmp);// dummy
			}
		} else if( auto assm = intp.assuming() ) {
			intp.discharge(ctxt.assume(*assm));
		} else {
			break;
		}
	}
	return tmp.impE(intp.subst(rule)).intro();
}
void import_all(Intp& intp) {
	auto ctxt = intp.ctxt();
	for(;;) {
		if( auto v = intp.fixing() ) {
			auto t = ctxt.fixes(*v);
			intp.instantiate( t ? *t : ctxt.fix(*v) );
		} else if( auto a = intp.assuming() ) {
			intp.discharge(ctxt.assume(*a));
		} else if( auto s = intp.obtaining() ) {
			auto [sym,thm] = *s;
			auto [sym_term,spec] = ctxt.obtain(sym,thm);
			intp.retain(sym_term,spec);
		} else {
			return;
		}
	}
}

