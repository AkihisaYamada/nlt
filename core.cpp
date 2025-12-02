#include<cstring>
#include"core.hpp"
#include"syntax.hpp"
using namespace std;

string const IMP = "⟹";
string const ALL = "∀";

string avoid(string_view const& var, function<bool(string_view const&)> const& test) {
	auto ret = string(var);
	while( test(ret) ) {
		ret.push_back('\'');
	}
	return ret;
}

static bool _eq_var(string const& x, string const& y, StrMap<unsigned int>& lmap, StrMap<unsigned int>& rmap ) {
	auto lopt = lmap.finds(x);
	auto ropt = rmap.finds(y);
	if( lopt ) {
		return ropt && lopt->second == ropt->second;
	}
	return !ropt && x == y;
}
bool Term::_eq(Term const& l, Term const& r, StrMap<unsigned int>& lmap, StrMap<unsigned int>& rmap, unsigned int depth) {
	if( auto lsym = l.sym() ) {
		if( auto rsym = r.sym() ) {
			return _eq_var(*lsym,*rsym,lmap,rmap);
		}
	} else if( auto lapp = l.app() ) {
		if( auto rapp = r.app() ) {
			return _eq(lapp->first,rapp->first,lmap,rmap,depth) &&
				_eq(lapp->second,rapp->second,lmap,rmap,depth);
		}
	} else if( auto lbind = l.bind() ) {
		if( auto rbind = r.bind() ) {
			depth++;
			auto const& linfo = lmap.emplace(lbind->first,depth);
			unsigned int lprev;
			if( linfo.second ) {
				lprev = 0;
			} else {
				lprev = linfo.first->second;
				linfo.first->second = depth;
			}
			auto const& rinfo = rmap.emplace(rbind->first,depth);
			unsigned int rprev;
			if( rinfo.second ) {
				rprev = 0;
			} else {
				rprev = rinfo.first->second;
				rinfo.first->second = depth;
			}
			if( _eq(lbind->second,rbind->second,lmap,rmap,depth) ) {
				if( lprev == 0 ) {
					lmap.erase(linfo.first);
				} else {
					linfo.first->second = lprev;
				}
				if( rprev == 0 ) {
					rmap.erase(rinfo.first);
				} else {
					rinfo.first->second = rprev;
				}
				return true;
			}
		}
	} else if( auto lunbind = l.unbind() ) {
		if( auto runbind = r.unbind() ) {
			return _eq_var(lunbind->first,runbind->first,lmap,rmap) &&
				_eq(lunbind->second,runbind->second,lmap,rmap,depth);
		}
	} else {
		assert(false);
	}
	return false;
}

void Term::_iter_syms(
	StrMSet& bsyms,
	function<void(string_view const&)> const& bsym,
	function<void(string_view const&)> const& fsym
) const {
	if( auto sym = this->sym() ) {
		if( bsyms.contains(*sym) ) {
			bsym(*sym);
		} else {
			fsym(*sym);
		}
	} else if( auto app = this->app() ) {
		app->first._iter_syms(bsyms,bsym,fsym);
		app->second._iter_syms(bsyms,bsym,fsym);
	} else if( auto abs = this->bind() ) {
		auto it = bsyms.insert(abs->first);
		abs->second._iter_syms(bsyms,bsym,fsym);
		bsyms.erase(it);
	} else if( auto fix = this->unbind() ) {
		if( bsyms.contains(fix->first) ) {
			bsym(fix->first);
		} else {
			fsym(fix->first);
		}
		fix->second._iter_syms(bsyms,bsym,fsym);
	} else {
		assert(false);
	}
}

Subst& Subst::_assign(string_view const& var, Term const& val) & {
	Opt<Term> r;
	if( var != val ) {
		_identity = false;
		r = val;
	}
	auto const& info = _map.emplace(var,r);
	if( !info.second ) {
		info.first->second = r;
	}
	return *this;
}

Term Term::subst(Subst const& subst) const {
	if( subst.identity() ) {
		return *this;
	}
	auto f = [&](string_view const& sym)->Opt<Term> {
		if( auto opt = subst.get(sym) ) {
			return *opt;
		}
		return {};
	};
	auto fixed = [&](string_view const& sym)->bool {
		return subst.ctxt().has_constant(sym);
	};
	return map(f,fixed);
}

static function<Term(string_view const&)> unit_map(string_view const& var, Term const& val) {
	return [&](auto sym){ return sym == var ? val : Term(sym); };
}
Term Term::subst(string_view const& var, CTerm const& val) const {
	if( val == var ) return *this;
	return map(
		unit_map(var,val),
		[&](auto sym)->Opt<Term>{
			if( auto t = val.ctxt().constant(sym) ) {
				return *t;
			}
			return {};
		}
	);
}

Opt<Term> Term::_Mapper::map( Term const& t ) {
	if( auto sym = t.sym() ) {
		return map_var(*sym);
	} else if( auto app = t.app() ) {
		auto [fun,arg] = *app;
		auto fun2 = map(fun);
		auto arg2 = map(arg);
		if( fun2 ) {
			if( arg2 ) {
				return (*fun2)(*arg2);
			}
			return (*fun2)(arg);
		}
		if( arg2 ) {
			return fun(*arg2);
		}
		return {};
	} else if( auto bind = t.bind() ) {
		auto const& var = bind->first;
		Term body = bind->second;
		Opt<Term> body2;
		string const& newvar = rename(var);
		auto newvar_info = bsyms.emplace(newvar,newvar);// the new name should be avoided
		if( newvar == var ) {// the bound variable is fresh
			body2 = map(body);
		} else {
			// replace the original name
			auto replace_info = bsyms.emplace(var,newvar);
			string prev;
			if( !replace_info.second ) {// the variable is bound multiple times
				prev = replace_info.first->second;// remember the old assignment
				replace_info.first->second = newvar;// update to the new name
			}
			body2 = map(body);
			// forget/recover replacement
			if( replace_info.second ) {
				bsyms.erase(replace_info.first);
			} else {
				replace_info.first->second = prev;
			}
		}
		// release the new name
		bsyms.erase(newvar_info.first);
		if( body2 ) {
			return newvar /= *body2;
		}
		return {};
	} else if( auto unbind = t.unbind() ) {// map(C[s])
		auto const& [C,s] = *unbind;
		Opt<Term> mapC = map_var(C);
		Opt<Term> maps = map(s);
		if( mapC ) {
			Term s2 = maps ? *maps : s;
			if( auto nsym = mapC->sym() ) {
				return *nsym %= s2;
			} else if( auto nabs = mapC->bind() ) {// (x. t)[s']
				auto const& [x,t] = *nabs;
				// return t[x := s'], where bound variables are avoided.
				auto avoided2 = [&]( string_view const& sym ) {
					return sym == x || avoided(sym) || bsyms.contains(sym);
				};
				return t.map(unit_map(x,s2),avoided2);
			} else {
				throw Error("#term")("\"bad unbind\"")(*mapC);
			}
		}
		if( maps ) {
			return C %= *maps;
		}
		return {};
	} else {
		assert(false);
	}
}

Term Term::inst(CTerm const& arg) const {
	auto a = bind();
	if( !a ) throw Error("#term")("\"bind expected\"")(*this)(arg);
	return a->second.subst(a->first,arg);
}

Ctxt::Ctxt() : Ctxt(Ref<Body>::make()) {
	_ref->fvars.insert(IMP);
	_ref->fvars.insert(ALL);
}

bool Ctxt::has_constant(string_view const& sym) const {
	if( fixes(sym) || obtains(sym) ) {
		return true;
	}
	if( auto parent = find_parent() ) {
		return parent->first.has_constant(sym);// TODO
	}
	return false;
}
CTerm Ctxt::enclose(Term const& t) {
	t.iter_syms( [&](auto sym){
		if( !has_constant(sym) ) {
			fix(sym);
		}
	} );
	return CTerm(*this,t);
}

CTerm Ctxt::fix(string_view const& s) {
	if( has_constant(s) ) {
DEB(*this);
		throw Error("#ctxt")("\"fixing fixed\"")(s);
	}
	_ref->modifiers.push_back(Fix(string(s)));
	_ref->fvars.emplace(s);
	return CTerm(*this,s);
}

pair<CTerm,Thm> Ctxt::obtain(string_view const& sym, Thm const& thm) {
	if( has_constant(sym) ) throw Error("#ctxt")("\"obtaining fixed\"")(sym);
	// thm should be ∀thesis. (∀sym'. props... ⟹ thesis) ⟹ thesis
	try {
		auto all1 = thm.binder(ALL);
		if( !all1 ) throw 0;
		auto thesis = all1->first;
		auto imp = all1->second.binary(IMP);
		if( !imp || imp->second != thesis ) throw 1;
		auto all2 = imp->first.unary(ALL);
		if( !all2 ) throw 2;
		auto abs = all2->bind();
		if( !abs ) throw 3;
		auto sym2 = abs->first;
		Term t = abs->second;// props... ⟹ thesis
		// check that props do not contain thesis
		Term const* in = &t;
		while( auto imp2 = in->binary(IMP) ) {
			auto& prop = imp2->first;
			prop.iter_syms(
				[&](auto str){ if( str == thesis ) throw 4; }
			);
			in = &imp2->second;
		}
		if( *in != thesis ) throw 5;
		// (props[var:=sym]... ⟹ thesis) ⟹ thesis
		auto sym_term = CTerm(*this,sym);
		Thm spec = CTerm( *this, thesis &= all2->inst(sym_term) >>= thesis );
		_ref->constants.emplace(sym);
		_ref->modifiers.push_back( Obtain(string(sym),thm,sym/=spec) );
		return {sym_term,spec};
	} catch ( int x ) {
		throw Error("#ctxt")("\"malformed obtain\"");
	}
}

Opt<Thm> Thm::discharges(Thm const& t) const {
	if( t.ctxt() != ctxt() ) throw Error("#thm")("\"wrong context discharge\"");
	if( auto const& imp = cbinary(IMP) )
	if( imp->first == t ) {
		return Thm(imp->second);
	}
	return {};
}

CTerm CTerm::intro() const {
	if( !_ctxt._ref->constants.empty() ) {// checks if obtained constants don't escape
		auto check = [&](auto v){
			if( _ctxt.obtains(v) ) { throw Error("#cterm")("\"constant escape\"")(v); }
		};
		iter_syms(check);
	}
	auto const& [parent,rev] = _ctxt.parent();
	Term stmt = *this;
	for( size_t i = _ctxt.revision(); i > 0; ) {
		i--;
		if( auto const& assm = _ctxt.assumed(i) ) {
			stmt = *assm >>= stmt;
		} else if( auto const& fix = _ctxt.fixed(i) ) {
			stmt = *fix &= stmt;
		} else if( auto const& obtain = _ctxt.obtained(i) ) {
			// obtain is safe
		} else {
			assert(false);
		}
	}
	return CTerm(parent,stmt);
}
Opt<tuple<string,Intp,CTerm>> CTerm::cbind() const {
	if( auto const& bind = Term::bind() ) {
		auto const& [var,body] = *bind;
		auto const& child = _ctxt.fork();
		auto var2 = avoid( var, [&](auto x){ return _ctxt.has_constant(x); } );
		return {{var2,child,CTerm(child.ctxt(),body.subst(var,child.ctxt().fix(var2)))}};
	}
	return {};
}
Opt<tuple<string,Intp,CTerm>> CTerm::cbinder( std::string_view const& b ) const {
	if( auto app = capp() )
	if( app->first == b ) {
		return app->second.cbind();
	}
	return {};
}
CTerm CTerm::lift( CTerm const& quantifier ) const {
	auto const& [parent,rev] = _ctxt.parent();
	if( quantifier.ctxt() != parent ) throw Error("#cterm")("\"wrong context lift\"");
	Term ret = *this;
	for( size_t i = _ctxt.revision(); i > 0; ) {
		i--;
		if( auto fix = _ctxt.fixed(i) ) {
			ret = ((Term)quantifier)( *fix /= ret );
		}
	}
	return CTerm(parent,ret);
}

CTerm Term::csubst(Subst const& subst) const {
	auto const& ctxt = subst.ctxt();
	auto fixed = [&](string_view const& sym)->Opt<Term> {
		if( auto t = subst.ctxt().constant(sym) ) {
			return *t;
		}
		return {};
	};
	if( subst.identity() ) {
		// only check that the term is closed.
		return ctxt.cterm(*this);
	}
	auto f = [&](string_view const& sym)->Opt<Term> {
		if( auto it = subst._map.find(sym); it != subst._map.end() ) {
			return it->second;
		} else if( ctxt.has_constant(sym) ) {
			return {};
		} else {
			throw UnboundVariable(sym);
		}
	};
	return CTerm(ctxt,map(f,fixed));
}

Intp Intp::make(Ctxt const& src, Ctxt const& tgt) {
	auto srcParent = src.find_parent();
	if( srcParent && srcParent->first != tgt ) throw Error(__func__)("\"wrong parent\"");
	return Intp(src,Subst(tgt),0);
}

Intp Intp::compose(Intp const& other) const {
	if( !other.ready() ) throw Error(__func__)("\"not ready\"");
	if( other._src != ctxt() ) throw Error(__func__)("\"wrong middle\"");
	auto subst = Subst(other.ctxt());
	for( auto [x,v] : _subst._map ) {
		if( v ) {
			subst.assign(x,v->subst(other));
			continue;
		}
		if( auto const& o = other._subst.map().finds(x) )
		if( auto o2 = o->second ) {
			subst._assign(x,*o2);
			continue;
		}
		subst._map.emplace(x,Opt<Term>());
	}
	return Intp(_src,std::move(subst),_rev);
}

