#include<string>
#include"util.hpp"

using namespace std;

Term const DUMMY = "?" /= Term("?");

Renamer avoider(Ctxt const& ctxt) {
	return [&](string_view const& v)->Opt<string>{
		return avoid(
			v[0] == '?' ? string("_")+v.substr(1) : v,
			[&]( string_view const& x ){ return (bool)ctxt.constant(x); }
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
Renamer patvar_maker() {
	return FreshMaker();
}
bool is_patvar( std::string_view const& sym ) {
	return !sym.empty() && sym[0] == '?';
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
	unsigned int depth = 0;
	Matcher( Ctxt const& valctxt, function<bool(string_view const&)> const& fvar ) : matcher(valctxt), fvar(fvar) {}
	Opt<Subst> matches( Term const& pat, CTerm const& val, Opt<Subst const&> subst ) && {
		if( match(pat,val,subst) ) {
			return std::move(matcher);
		}
		return {};
	}
	bool val_closed( Term const& val ) const {
		StrMSet bounds;
		return val_closed(val,bounds);
	}
	bool val_closed( Term const& val, StrMSet& bounds ) const& {
		if( auto sym = val.sym() ) {
			return bounds.contains(*sym) || !rinds.contains(*sym);
		}
		if( auto bind = val.bind() ) {
			auto [var,body] = *bind;
			auto it = bounds.insert(var);
			auto ret = val_closed(body,bounds);
			bounds.erase(it);
			return ret;
		}
		if( auto app = val.app() ) {
			return val_closed(app->first,bounds) && val_closed(app->second,bounds);
		}
		if( auto unbind = val.unbind() ) {
			return val_closed(unbind->second,bounds);
		}
		assert(false);
	}
	bool bind( Term const& l, Term const& r, function<bool( Term const&, Term const& )> const& inner ) {
		if( auto const& labs = l.bind() ) {
			if( auto const& rabs = r.bind() ) {
				auto const& [x,pat2] = *labs;
				auto const& [y,val2] = *rabs;
				auto const& lind_info = linds.emplace(x,depth);
				auto const& rind_info = rinds.emplace(y,depth);
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
					depth--;
					return true;
				}
			}
		}
		return false;
	}
	bool match( Term const& pat, Term const& val, Opt<Subst const&> subst ) {
		if( auto sym = pat.sym() ) {// pat is a symbol
			if( auto lind = linds.finds_value(*sym) ) {// pat is a bound variable
				if( auto rsym = val.sym() ) {// val must be a bound variable of the same index
					return rinds.finds_value(*rsym) == lind;
				}
				return false;
			}
			if( subst ) if( auto const& act = subst->get(*sym) ) {// actually substituted
				return match(*act,val,{});
			}
			if( auto const& map_opt = matcher.get(*sym) ) {// already assigned variable
				return *map_opt == val;// equal as term
			}
			if( fvar(*sym) ) {// free variable can be assigned, if val does not contain bound variables
				if( val_closed(val) )
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
				return match(lapp->first,rapp->first,subst) &&
					match(lapp->second,rapp->second,subst);
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
						bool ret = match(pat2,val2,subst);
						escaped_var.erase(it.first);
						return ret;
					}
					if( auto const& bind = xval->bind() ) {// X is assigned to a binding
						auto const& [y,vbody] = *bind;
						auto it = escaped_var.insert(x);// inside the body, X is escaping
						bool ret = eq_upto(subst,vbody,val,y,pat2);// the body must be equal to val up to y
						escaped_var.erase(it.first);
						return ret;
					}
					return false;
				}
				if( fvar(x) ) {// applied pattern variable
					if( auto var = pat2.sym() )
					if( auto ind = linds.finds_value(*var) ) {// higher order pattern
						if( auto abs = matcher.ctxt().closed(rbvars[*ind]/=val) ) {
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
					return match(pat2,val2,subst);
				}
			}
			// otherwise, pat and val must have the same shape
			auto vfix = val.unbind();
			if( !vfix ) {
				return false;
			}
			auto [y,val2] = *vfix;
			if( auto lind = linds.finds_value(x) ) {// x is a bound variable
				if( rinds.finds_value(y) != lind ) return false;
			} else {// x is a constant
				if( rinds.finds_value(y) ) return false;
				if( x != y ) return false;
			}
			return match(pat2,val2,subst);
		}
		return bind(pat, val, [this,&subst]( auto pat, auto val ){ return match(pat,val,subst); } );
	}
	bool eq_upto( Opt<Subst const&> subst, Term const& l, Term const& r, string const& var, Term const& pat ) {
		if( auto const& sym = l.sym() ) {
			if( *sym == var ) {// reached the unbound variable. Go back to matching
				return match(pat,r,subst);
			}
			return l == r;
		}
		if( auto const& lapp = l.app() ) {
			auto const& rapp = r.app();
			return rapp && eq_upto(subst,lapp->first,rapp->first,var,pat) &&
				eq_upto(subst,lapp->second,rapp->second,var,pat);
		}
		if( auto const& lfix = l.unbind() ) {
			auto const& rfix = r.unbind();
			return rfix && lfix->first == rfix->first && eq_upto(subst,lfix->second,rfix->second,var,pat);
		}
		return bind(l, r, [&]( auto l, auto r ){ return eq_upto(subst,l,r,var,pat); } );
	}
};

Opt<Subst> match( Term const& pat, CTerm const& val, function<bool(string_view const&)> const& fvar, Opt<Subst const&> subst ) {
	return Matcher(val.ctxt(),fvar).matches(pat,val,subst);
}
pair<Thm,size_t> strip_all( Thm const& thm, Ctxt& ctxt, Renamer const& renamer ) {
	pair<Thm,size_t> ret = {thm,0};
	auto loc = thm.ctxt();
	while( auto all = ret.first.binder(ALL) ) {
		auto [v,b] = *all;
		auto nv = renamer(v);
		if( !nv ) break;
		ret.second++;
		ret.first = ret.first.allE(loc.weaken(ctxt.fix(*nv)));
	}
	return ret;
}
CTerm strip_all(CTerm t, Ctxt& ctxt, Renamer const& renamer) {
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
	Thm rule = strip_all(match_ctxt.weaken(thm),match_ctxt).first;
	auto const& imp = rule.cbinary(IMP);
	if( !imp ) throw Error("#match_discharge")(thm);
	auto const& arg_weaken = arg.subst(thm2assm);
	auto m = match( imp->first, arg_weaken, [&](auto v){ return rule.ctxt().fixes(v); } );
	if( !m ) throw Error("#match_discharge")(thm)(arg);
	rule = rule.impE(match_ctxt.assume(imp->first));
	auto match2assm = Intp::make(match_ctxt,assm_ctxt);
	subst_intp(match2assm,*m);
	auto const& assm = match2assm.assuming();
	assert(assm);
	match2assm.discharge(arg_weaken);
	return rule.subst(match2assm).intro();
}
