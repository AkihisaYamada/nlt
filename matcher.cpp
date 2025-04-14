#include"util.hpp"

using namespace std;

Term const DUMMY = "_" /= Term("_");

Renamer avoider(Ctxt& ctxt) {
	return [&](string_view const& v)->Opt<string>{
		return avoid(v,[&](string_view const& x){ return ctxt.constant(x); });
	};
}
class FreshMaker {
	int i = 0;
public:
	string operator()( string_view const& ) {
		i++;
		return "?" + std::to_string(i);
	}
};
Renamer fresh_maker() {
	return FreshMaker();
}


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

Opt<std::string> virtual_var( CTerm const& t ) {
	if( auto sym = t.sym() ) {
		return *sym;
	}
	if( auto abs = t.cbind() )
	if( auto fix = abs->second.cunbind() ) {
		auto [v,_,arg] = *fix;
		return v;
	}
	return {};
}
template<class T>
Opt<size_t> find_last( std::vector<T> const& haystack, T const& needle ) {
	for( size_t i = haystack.size(); i != 0; ) {
		i--;
		if( haystack[i] == needle ) {
			return i;
		}
	}
	return {};
}

struct Matcher {
	Subst matcher;
	StrSet escaped_var;// in α.[...α...], second α is escaping
	function<bool(string_view const&)> const& fvar;
	StrMap<unsigned int> linds;
	vector<string> rbvars;
	StrMap<unsigned int> rinds;
	unsigned int depth = 0;
	Matcher( Ctxt const& ctxt, function<bool(string_view const&)> const& fvar ) : matcher(ctxt), fvar(fvar) {}
	Opt<Subst> matches( CTerm const& pat, CTerm const& val ) && {
		if( match(pat,val) ) {
			return std::move(matcher);
		}
		return {};
	}
	bool match(CTerm const& pat, CTerm const& val) {
		if( auto sym = pat.sym() ) {// pat is a symbol
			if( auto lind = linds.finds(*sym) ) {// pat is a bound variable
				if( auto rsym = val.sym() ) {// val must be a bound variable of the same index
					return rinds.finds(*rsym) == lind;
				}
				return false;
			} else if( auto const& map_opt = matcher.get(*sym) ) {// already assigned variable
				return (Term)*map_opt == val;// equal as term (may belong to different context)
			} else if( fvar(*sym) ) {// free symbol
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
				return match(app->first,app2->first) &&
					match(app->second,app2->second);
			}
			return false;
		} else if( auto const& abs = pat.cbind() ) {
			if( auto const& abs2 = val.cbind() ) {
				string const& x = abs->first;
				string const& y = abs2->first;
				auto const& lind_info = linds.insert({x,depth});
				auto const& rind_info = rinds.insert({y,depth});
				rbvars.emplace_back(y);
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
				depth++;
				if( match(abs->second,abs2->second) ) {
					// recover the old indices
					rbvars.pop_back();
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
		} else if( auto fix = pat.cunbind() ) {// x.[s]
			auto [x,_,pat2] = *fix;
			if( !escaped_var.contains(x) ) {// this x is from the pattern side.
				auto const& opt = matcher.get(x);
				if( opt ) {// the context is assigned
					if( auto const& sym = opt->sym() ) {// x is assigned to a variable, then rhs must have the same shape
						auto fix2 = val.cunbind();
						if( !fix2 ) {
							return false;
						}
						auto [y,_,val2] = *fix2;
						if( *sym != y ) {
							return false;
						}
						auto it = escaped_var.insert(x);// inside the argument, x is escaping
						bool ret = match(pat2,val2);
						escaped_var.erase(it.first);
						return ret;
					}
					if( auto const& abs = opt->bind() ) {// the context is instantiated
						auto it = escaped_var.insert(x);// inside the argument, x is escaping
						bool ret = match(opt->inst(pat2),val);
						escaped_var.erase(it.first);
						return ret;
					}
					return false;
				}
				if( fvar(x) ) {// applied pattern variable
					if( auto var = pat2.sym() ) if( auto ind = linds.finds(*var) ) {// higher order pattern
						if( auto abs = matcher.ctxt().closed(rbvars[ind->second]/=val) ) {
							matcher.assign(x,*abs);
							return true;
						}
						return false;
					}
					// otherwise, val must also be abstraction
					auto vfix = val.cunbind();
					if( !vfix ) {
						return false;
					}
					auto const& [y,cy,val2] = *vfix;
					if( x != y ) {
						auto const& cy2 = matcher.ctxt().constant(y);
						if( !cy2 ) {// bound variable cannot be matched
							return false;
						}
						matcher.assign(x,*cy2);
					}
					return match(pat2,val2);
				}
			}
			// otherwise, pat and val must have the same shape
			auto vfix = val.cunbind();
			if( !vfix ) {
				return false;
			}
			auto [y,cy,val2] = *vfix;
			if( x != y ) {
				return false;
			}
			return match(pat2,val2);
		} else {
			assert(false);
		}
	}
};

Opt<Subst> match( CTerm const& pat, CTerm const& val, function<bool(string_view const&)> const& fvar ) {
	return Matcher(val.ctxt(),fvar).matches(pat,val);
}
pair<Thm,size_t> strip_all( Thm const& thm, Ctxt& ctxt, Renamer const& renamer ) {
	pair<Thm,size_t> ret = {thm,0};
	ret.first = thm.weaken(ctxt);
	while( auto all = ret.first.binder(ALL) ) {
		auto [v,b] = *all;
		auto nv = renamer(v);
		if( !nv ) break;
		ret.second++;
		ret.first = ret.first.instantiate(ctxt.fix(*nv));
	}
	return ret;
}
CTerm strip_all(CTerm t, Ctxt& ctxt, Renamer const& renamer) {
	t = t.weaken(ctxt);
	auto subst = Subst(ctxt);
	for(;;) {
		auto all = t.cbinder(ALL);
		if( !all ) break;
		auto const& v = all->first;
		auto nv = renamer(v);
		if( !nv ) break;
		auto nvt = ctxt.fix(*nv);
		subst.assign(v,nvt);
		t = all->second;
	}
	return t.csubst(subst);
}

void subst_intp( Intp& intp, Subst& subst ) {
	while( auto const& sym = intp.modification().ref<Intp::Fix>() ) {
		auto const& val = subst.get(*sym);
		auto ctxt = subst.ctxt();
		intp.instantiate( val ? *val : ctxt.fix(*avoider(ctxt)(*sym)));
	}
}

Thm match_discharge( Thm const& thm, Thm const& arg ) {
	Ctxt ctxt = thm.ctxt().branch();
	Ctxt rule_ctxt = ctxt.branch();
	Thm rule = strip_all(thm,rule_ctxt,fresh_maker()).first;
	auto const& imp = rule.cbinary(IMP);
	if( !imp ) throw Error("#match_discharge")(thm);
	auto const& arg_weaken = arg.weaken(ctxt);
	auto m = match( imp->first, arg_weaken, [&](auto v){ return rule.ctxt().fixes(v); } );
	if( !m ) throw Error("#match_discharge")(thm)(arg);
	rule = rule.discharge(rule_ctxt.assume(imp->first));
	auto intp = Intp(rule_ctxt,ctxt);
	subst_intp(intp,*m);
	auto const& assm = intp.modification().ref<Intp::Assume>();
	assert(assm);
	intp.discharge(arg_weaken);
	return intp.subst(rule).intro();
}
