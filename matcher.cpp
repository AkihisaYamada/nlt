#include<string>
#include"util.hpp"

using namespace std;

Term const DUMMY = "?" /= Term("?");

Renamer avoider(Ctxt const& ctxt) {
	return [&](string_view const& v)->Opt<string>{
		return avoid(
			v[0] == '?' ? string("_")+v.substr(1) : v,
			[&]( string_view const& x ){ return ctxt.constant(x); }
		);
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
	if( auto fix = get<2>(*abs).cunbind() ) {
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
	Intp lweaken;
	unsigned int depth = 0;
	Matcher( Ctxt const& patctxt, Ctxt const& valctxt, function<bool(string_view const&)> const& fvar ) : matcher(valctxt), fvar(fvar), lweaken(patctxt.self()) {}
	Opt<Subst> matches( CTerm const& pat, CTerm const& val ) && {
		if( match(pat,val) ) {
			return std::move(matcher);
		}
		return {};
	}
	bool abs( Term const& l, Term const& r, function<bool( Term const&, Term const& )> const& inner ) {
		if( auto const& labs = l.bind() ) {
			if( auto const& rabs = r.bind() ) {
				auto const& [x,pat2] = *labs;
				auto const& [y,val2] = *rabs;
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
				if( inner(pat2,val2) ) {
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
			}
		}
		return false;
	}

	bool match(Term const& pat, Term const& val) {
		if( auto sym = pat.sym() ) {// pat is a symbol
			if( auto lind = linds.finds(*sym) ) {// pat is a bound variable
				if( auto rsym = val.sym() ) {// val must be a bound variable of the same index
					return rinds.finds(*rsym) == lind;
				}
				return false;
			}
			if( auto const& map_opt = matcher.get(*sym) ) {// already assigned variable
				return *map_opt == val;// equal as term
			}
			if( fvar(*sym) ) {// free variable can be assigned, if val is does not contain bound variables
				if( auto cval = matcher.ctxt().closed(val) ) {
					matcher.assign(*sym,*cval);
					return true;
				}
				return false;
			}
			return *sym == val;// otherwise, val must be the same constant.
		}
		if( auto lapp = pat.app() ) {
			if( auto rapp = val.app() ) {
				return match(lapp->first,rapp->first) &&
					match(lapp->second,rapp->second);
			}
			return false;
		}
		if( auto fix = pat.unbind() ) {// X.[s]
			auto [x,pat2] = *fix;
			if( !escaped_var.contains(x) ) {// this X is in the scope
				if( auto const& xval = matcher.get(x) ) {// X is assigned
					if( auto const& sym = xval->sym() ) {// X is assigned to a variable, then rhs must have the same shape
						auto const& vfix = val.unbind();
						if( !vfix ) {
							return false;
						}
						auto [y,val2] = *vfix;
						if( *sym != y ) {
							return false;
						}
						auto it = escaped_var.insert(x);// inside the body, X is escaping
						bool ret = match(pat2,val2);
						escaped_var.erase(it.first);
						return ret;
					}
					if( auto const& bind = xval->bind() ) {// X is assigned to a binding
						auto const& [y,vbody] = *bind;
						auto it = escaped_var.insert(x);// inside the body, X is escaping
						bool ret = eq_upto(vbody,val,y,pat2);// the body must be equal to val up to y
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
					auto vfix = val.unbind();
					if( !vfix ) {
						return false;
					}
					auto const& [y,val2] = *vfix;
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
			auto vfix = val.unbind();
			if( !vfix ) {
				return false;
			}
			auto [y,val2] = *vfix;
			if( x != y ) {
				return false;
			}
			return match(pat2,val2);
		}
		return abs(pat, val, [this]( auto pat, auto val ){ return match(pat,val); } );
	}
	bool eq_upto( Term const& l, Term const& r, string const& var, Term const& pat ) {
		if( auto const& sym = l.sym() ) {
			if( *sym == var ) {// reached the unbound variable. Go back to matching
				return match(pat,r);
			}
			return l == r;
		}
		if( auto const& lapp = l.app() ) {
			auto const& rapp = r.app();
			return rapp && eq_upto(lapp->first,rapp->first,var,pat) &&
				eq_upto(lapp->second,rapp->second,var,pat);
		}
		if( auto const& lfix = l.unbind() ) {
			auto const& rfix = r.unbind();
			return rfix && lfix->first == rfix->first && eq_upto(lfix->second,rfix->second,var,pat);
		}
		return abs(l, r, [&]( auto l, auto r ){ return eq_upto(l,r,var,pat); } );
	}
};

Opt<Subst> match( CTerm const& pat, CTerm const& val, function<bool(string_view const&)> const& fvar ) {
	return Matcher(pat.ctxt(),val.ctxt(),fvar).matches(pat,val);
}
pair<Thm,size_t> strip_all( Thm const& thm, Intp const& toChild, Renamer const& renamer ) {
	pair<Thm,size_t> ret = {thm.subst(toChild),0};
	auto ctxt = toChild.ctxt();
	while( auto all = ret.first.binder(ALL) ) {
		auto [v,b] = *all;
		auto nv = renamer(v);
		if( !nv ) break;
		ret.second++;
		ret.first = ret.first.instantiate(ctxt.fix(*nv));
	}
	return ret;
}
CTerm strip_all(CTerm t, Intp const& child, Renamer const& renamer) {
	t = t.subst(child);
	auto ctxt = child.ctxt();
	auto subst = Subst(ctxt);
	for(;;) {
		auto a = t.cunary(ALL);
		if( !a ) break;
		auto b = a->bind();
		if( !b ) break;
		auto const& v = b->first;
		auto nv = renamer(v);
		if( !nv ) break;
		auto nvt = ctxt.fix(*nv);
		subst.assign(v,nvt);
		t = a->inst(nvt);
	}
	return t.csubst(subst);
}

void subst_intp( Intp& intp, Subst& subst ) {
	while( auto const& sym = intp.fixing() ) {
		auto const& val = subst.get(*sym);
		auto ctxt = subst.ctxt();
		intp.instantiate( val ? *val : ctxt.fix(*avoider(ctxt)(*sym)));
	}
}

Thm match_discharge( Thm const& thm, Thm const& arg ) {
	auto thm_ctxt = thm.ctxt();
	auto thm2assm = thm_ctxt.fork();
	auto assm_ctxt = thm2assm.ctxt();
	auto assm2match = assm_ctxt.fork();
	auto match_ctxt = assm2match.ctxt();
	auto thm2match = thm2assm.compose(assm2match);
	Thm rule = strip_all(thm,thm2match).first;
	auto const& imp = rule.cbinary(IMP);
	if( !imp ) throw Error("#match_discharge")(thm);
	auto const& arg_weaken = arg.subst(thm2assm);
	auto m = match( imp->first, arg_weaken, [&](auto v){ return rule.ctxt().fixes(v); } );
	if( !m ) throw Error("#match_discharge")(thm)(arg);
	rule = rule.discharge(match_ctxt.assume(imp->first));
	auto match2assm = Intp::make(match_ctxt,assm_ctxt);
	subst_intp(match2assm,*m);
	auto const& assm = match2assm.assuming();
	assert(assm);
	match2assm.discharge(arg_weaken);
	return rule.subst(match2assm).intro();
}
