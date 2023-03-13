#include"util.hpp"

using namespace std;

ostream& operator<<(ostream& os, Term const& t) {
	if( auto sym = t.sym() ) {
		return os << *sym;
	} else if( auto const& app = t.app() ) {
		return os << '(' << app->first << ' ' << app->second << ')';
	} else if( auto const& abs = t.abs() ) {
		return os << abs->first << ". " << abs->second;
	} else if( auto const& fix = t.fix() ) {
		return os << fix->first << ".[" << fix->second << ']';
	} else {
		assert(false);
	}
}
ostream& operator<<(ostream& os, CSubst const& subst) {
	char const* punct = "[ ";
	for( auto const& x : subst.map() ) {
		os << punct << x.first << " := " << x.second;
		punct = ",\n  ";
	}
	return os << "\n]";
}

pair<String, list<Term>> uncurry(Term const& t) {
	Term const* cur = &t;
	list<Term> args;
	for(;;) {
		if( auto p = cur->app() ) {
			args.push_front(p->second);
			cur = &p->first;
		} else if( auto sym = cur->sym() ) {
			return pair<String,list<Term>>(*sym,args);
		} else {
			throw UnexpectedTerm(*cur);
		}
	}
}

static bool match(StrSet const& fsyms, CTerm const& pat, CTerm const& val, CSubst& matcher, StrMap<unsigned int>& lidx, StrMap<unsigned int>& ridx, unsigned int depth) {
//cerr << "match: "<< pat << endl << '\t' << val << endl;
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
	} else if( auto app = pat.app() ) {
		if( auto app2 = val.app() ) {
			return match(fsyms,app->first,app2->first,matcher,lidx,ridx,depth) &&
				match(fsyms,app->second,app2->second,matcher,lidx,ridx,depth);
		} else {
			return false;
		}
	} else if( auto const& abs = pat.abs() ) {
		if( auto const& abs2 = val.abs() ) {
			String const& x = abs->first;
			String const& y = abs2->first;
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
	} else if( auto fix = pat.fix() ) {
		auto const& x = fix->first;
		if( auto const& opt = matcher.get(x) ) {
			if( auto const& abs = opt->abs() ) {
				return match(fsyms,opt->inst(fix->second),val,matcher,lidx,ridx,depth);
			}
		}
		if( auto fix2 = val.fix() ) {
			if( fsyms.contains(x) ) {
				matcher.assign(x,fix2->first);
			}
			return match(fsyms,fix->second,fix2->second,matcher,lidx,ridx,depth);
		} else {
			return false;
		}
	} else {
		assert(false);
	}
}

optional<CSubst> match(StrSet const& fsyms, CTerm const& pat, CTerm const& val) {
	CSubst ret = val.ctxt();
	StrMap<unsigned int> lidx, ridx;
	if( match(fsyms,pat,val,ret,lidx,ridx,0) ) {
		return ret;
	}
	return optional<CSubst>();
}
Term strip_all(Term t, Ctxt& ctxt) {
	for(;;) {
		if( auto app = t.app() ) {
			if( app->first == ALL ) {
				if( auto abs = app->second.abs() ) {
					String const& v = abs->first;
					String nv = avoid(v,[&](String const& x){ return ctxt.find_sym(x); });
					t = abs->second.subst(abs->first,ctxt.fix(nv));
					continue;
				}
			}
		}
		return t;
	}
}
Thm strip_all(Thm thm, Ctxt& ctxt) {
	thm = thm.weaken(ctxt);
	for(;;) {
		if( auto const& app = thm.app() ) {
			if( app->first == ALL ) {
				if( auto const& abs = app->second.abs() ) {
					String const& v = abs->first;
					String nv = avoid(v,[&](String const& x){ return ctxt.find_sym(x); });
					thm = thm.allE(ctxt.fix(nv));
					continue;
				}
			}
		}
		return thm;
	}
}
CTerm strip_all(CTerm t, Ctxt& ctxt) {
	t = t.weaken(ctxt);
	for(;;) {
		if( auto app = t.app() ) {
			if( app->first == ALL ) {
				if( auto abs = app->second.abs() ) {
					String const& v = abs->first;
					String nv = avoid(v,[&](String const& x){ return ctxt.find_sym(x); });
					t = app->second.inst(ctxt.fix(nv));
					continue;
				}
			}
		}
		return t;
	}
}

Thm discharge(Thm thm, Thm arg) try {
	Ctxt ctxt = thm.ctxt();
	// expand thm into cond ⟹ concl
	Ctxt thm_ctxt = ctxt.branch();
	Thm thm_strip = strip_all(thm,thm_ctxt);
	auto const& app1 = thm_strip.app();
	if( !app1 ) throw 0;
	auto const& app2 = app1->first.app();
	if( !app2 ) throw 1;
	if( app2->first != IMP ) throw 2;
	// expand cond
	CTerm cond = app2->second;
	Ctxt cond_ctxt = thm_ctxt.branch();
	CTerm cond_strip = strip_all(cond,cond_ctxt);
	// expand arg
	Ctxt arg_ctxt = cond_ctxt.branch();
	Thm arg_strip = strip_all(arg,arg_ctxt);
	cond_strip = cond_strip.weaken(arg_ctxt);
	cond = cond.weaken(arg_ctxt);
	optional<CSubst> unifier = unify(cond_strip,arg_strip,[&](String const& x){
		return thm_ctxt.fvars().contains(x) || arg_ctxt.fvars().contains(x);
	} );
	if( !unifier ) throw 3;
	// unassigned free variables will be universally quantified in the result
	Ctxt ret_ctxt = ctxt.branch();
	for( auto const& x : arg_ctxt.fvar_list() ) {
		if( !unifier->map().contains(x) ) {
			ret_ctxt.fix(x);
		}
	}
	for( auto const& x : thm_ctxt.fvar_list() ) {
		if( !unifier->map().contains(x) ) {
			ret_ctxt.fix(x);
		}
	}
	// instantiating arg according to the unifier
	// quantify variables as cond
	Ctxt discharger_ctxt = ret_ctxt.branch();
	for( auto const& x : cond_ctxt.fvar_list() ) {
		discharger_ctxt.fix(x);
	}
	arg = arg.weaken(discharger_ctxt);
	for( auto const& x : arg_ctxt.fvar_list() ) {// TODO: slower than `subst`
		auto val = unifier->get(x);
		arg = arg.allE( discharger_ctxt.cterm( val ? (Term)*val : x ) );
	}
	arg = arg.intro();
	thm = thm.weaken(ret_ctxt);
	for( auto const& x : thm_ctxt.fvar_list() ) {// TODO: slower than `subst`
		auto val = unifier->get(x);
		thm = thm.allE( ret_ctxt.enclose( val ? (Term)*val : x ) );
	}
	thm = thm.impE(arg);
	thm = thm.intro();
	return thm;
} catch( int n ) {
	throw MalformedDischarge(thm,arg);
}


Thm Concluder::conclude(Thm const& thm) {
	auto const& app1 = thm.app();
	assert(app1);
	auto const& app2 = app1->first.app();
	assert(app2);
	CTerm const& source = app2->second; // thm = source ⟹ ...
	for( Rule const& rule : rules ) {
		auto const& pat_ctxt = rule.pat.ctxt();
		if( auto const& m = match(pat_ctxt.fvars(),rule.pat,source) ) {
			Thm arg = rule.thm.weaken(source.ctxt());
			for( auto const& fvar : pat_ctxt.fvar_list() ) {
				arg = arg.allE(*m->get(fvar));
			}
			return thm.impE(arg);
		}
	}
	throw UnexpectedTerm(thm);
}

