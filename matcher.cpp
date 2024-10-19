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

void import_all(Intp& intp) {
	auto ctxt = intp.ctxt();
	for(;;) {
		if( auto v = intp.fixing() ) {
			intp.instantiate(ctxt.fix(*v));
		} else if( auto a = intp.assuming() ) {
			intp.discharge(ctxt.assume(*a));
		} else if( auto s = intp.obtaining() ) {
			auto [sym,thms] = ctxt.obtain(*s);
			intp.retain(sym,thms);
		} else {
			return;
		}
	}
}

