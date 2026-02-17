#include <iostream>
#include "inference.hpp"

using namespace std;

string const Rewrite::CONG = "#cong";

Opt<tuple<string,Term,Term>> strips_binary( Term const& term ) {
	if( auto const& app = term.app() )
	if( auto const& app2 = app->first.app() )
	if( auto const& rel = app2->first.sym() ) {
		return {{*rel,app2->second,app->second}};
	}
	return {};
}
Opt<tuple<string,CTerm,CTerm>> strips_binary( CTerm const& term ) {
	if( auto const& app = term.capp() )
	if( auto const& app2 = app->first.capp() )
	if( auto const& rel = app2->first.sym() ) {
		return {{*rel,app2->second,app->second}};
	}
	return {};
}

/** accesses the binary operator */
Opt<string const&> gets_binary_sym( Term const& term ) {
	if( auto const& app = term.app() )
	if( auto const& app2 = app->first.app() ) {
		return app2->first.sym();
	}
	return {};
}
Opt<string const&> gets_binary_sym( Term&& term ) = delete;// for memory safety

Thm Thy::dualize( Thm const& thm, Resolver& resolver ) const & {
	Thy subthy = branch();
	Thm body = subthy.weaken(thm);
	for(;;) {
		body = strip_all(body,subthy.self()).first;
		auto imp = body.cbinary(IMP);
		if(!imp) break;
		Thm assm = subthy.assume(imp->first);
		add_intro(subthy,assm);
		body = body.discharge(assm);
	}
	if( auto const& bin = strips_binary(body) )
	if( auto const& ind = rewriter()->gets_rel_ind(get<0>(*bin)) ) {
		auto const& dual = rewriter()->_duals.finds(*ind);
		if( !dual ) throw Error("\"no dual rule for\"")(get<0>(*bin));
		Thm dual_thm = subthy.weaken(dual->second.thm) << body;
		while( auto o = resolver.discharges(subthy,dual_thm,false) ) {
			dual_thm = *o;
		}
		return dual_thm.intro();
	}
	throw Error("\"not dualizable\"")(body);
}

void Thy::add_rewrite_rule( Rewrite::Rules& rules, Thm const& thm, bool cong ) const & {
	auto const& [ind,rel,rule] = rewriter()->make_rule(thm,cong);
	rules[ind].emplace_back(std::move(rule));
}

void Rewrite::register_imp( Thm const& thm, bool dir ) & {
	auto rule = strip_all(thm,thm.ctxt().fork(),patvar_maker()).first;// x = y ⟹ conds... ⟹ x ⟹ y
	if( auto const& imp = rule.cbinary(IMP) )// conds... ⟹ x ⟹ y
	if( auto const& imp2 = imp->second.cbinary(IMP) )
	if( auto const& rel = gets_binary_sym(imp->first) ) {
		auto const& ind = gets_rel_ind(*rel);
		if( !ind ) throw Error("\"unregistered relation\"")(*rel);
		Term t = imp2->second;
		size_t conds = 0;
		while( auto imp3 = t.binary(IMP) ) {
			t = imp3->second;
			conds++;
		}
		( dir ? _imps : _revimps ).emplace(*ind,Imp{thm,conds});
		return;
	}
	throw Error("\"malformed imp\"")(thm);
}
bool Rewrite::register_refl( Thm const& thm, bool def ) & {
	auto rule = Intro::rule(thm);
	auto const& rel = gets_binary_sym(rule.conclusion());
	if( !rel ) throw Error("\"malformed refl\"")(thm);
	if( gets_rel_ind(*rel) ) {
		return false;
	}
	size_t ind = _rels.size();
	_rels.emplace_back(*rel);
	_rel2ind.emplace(*rel,ind);
	_refls.emplace_back(thm);
	_congs.emplace_back();
	if( def ) {
		_default_ind = ind;
	}
	return true;
}
void Rewrite::register_trans( Thm const& thm ) & {
	auto rule = Intro::rule(thm);// ∀x y, x = y, ∀z, y = z, φ... ⊢ x = z
	auto xz = rule.conclusion();
	Ctxt ctxt = xz.ctxt();
	if( ctxt.fixed(0) && ctxt.fixed(1) )
	if( auto const& xy = ctxt.assumed(2) )
	if( auto const& rel1 = gets_binary_sym(*xy) )
	if( ctxt.fixed(3) )
	if( auto const& yz = ctxt.assumed(4) )
	if( auto const& rel2 = gets_binary_sym(*yz) )
	if( auto const& rel3 = gets_binary_sym(xz) )
	if( *rel1 == *rel2 && *rel2 == *rel3 )
	if( auto const& ind = gets_rel_ind(*rel1) ) {
		_trans.emplace(*ind,thm);
		return;
	}
	throw Error("\"malformed trans\"")(thm);
}
tuple<char,std::string,Rewrite::Rule> Rewrite::make_rule( Thm const& thm, bool cong ) const& {
	// parsing congruence rule
	auto intro = Intro::rule(thm);// e.g. ∀x y, (φ ⟹... x = y), ∀x2 y2, ... ⊢ l[x...] = r[y...]
	auto const& bin = strips_binary(intro.conclusion());
	if( !bin ) throw Error("\"rewrite rule expects binary conclusion\"")(intro.conclusion());
	auto const& [rel,tmp_l,tmp_r] = *bin;
	auto const& ind = gets_rel_ind(rel);
	if( !ind ) throw Error("\"unregistered rewrite relation\"")(rel);
	Intp thy2rule = thm.ctxt().fork();
	Ctxt rule_ctxt = thy2rule.ctxt();
	auto l = rule_ctxt.enclose(tmp_l);// first fix lhs variables
	vector<Rule::Cond> conds;
	vector<Thm> cond_thms;
	Ctxt tmp_ctxt = intro.conclusion().ctxt();
	for( size_t rev = 0;; rev++ ) {
		if( tmp_ctxt.fixed(rev) ) {
			continue;
		} else if( auto assm = tmp_ctxt.assumed(rev) ) {// condition or guard
			Intp loc2cond = rule_ctxt.fork();
			Ctxt cond_ctxt = loc2cond.ctxt();
			Term body = *assm;
			bool abs;
			if( auto all = body.binder(ALL) ) {// TODO: improve?
				cond_ctxt.fix(all->first);
				body = all->second;
				abs = true;
			} else {
				abs = false;
			}
			for(;;) {
				if( auto x = strips_binary(body) ) {
					auto const& [rel,s,t] = *x;
					if( rel == IMP ) {// guarded condition
						auto guard = cond_ctxt.closed(s);
						if( !guard ) throw Error("\"open guarded condition\"")(body)(thm);
						cond_ctxt.assume(*guard);
						body = t;
						continue;
					}
					if( auto ind = gets_rel_ind(rel) ) {// rewrite condition
						auto cond_lhs = cond_ctxt.closed(s);
						if( !cond_lhs ) throw Error("\"open condition lhs\"")(s)(thm);
						auto cond = rule_ctxt.assume((Term)*assm);//TODO: reduce double-check
						if( abs && !t.unbind() ) throw Error("\"unsupported condition\"")(t)(thm);
						conds.emplace_back(ind,abs,true,cond);
						cond_thms.emplace_back(std::move(cond));
						break;
					}
				}
				auto cond_conc = cond_ctxt.closed(body);
				if( !cond_conc ) throw Error("\"open guard\"")(body)(thm);
				auto cond = rule_ctxt.assume(cond_conc->intro());
				conds.emplace_back(Opt<size_t>{},false,body.sym(),cond);
				cond_thms.emplace_back(std::move(cond));
				break;
			}
			continue;
		} else {
			break;
		}
	}
	auto r = rule_ctxt.closed(tmp_r);
	if( !r ) throw Error("\"open rhs\"")(thm);
	// finally instantiate to new form
	auto tmp2rule = Intp::make(tmp_ctxt,thm.ctxt()).compose(thy2rule);
	auto condi = cond_thms.begin();
	for(;;) {
		if( auto sym = tmp2rule.fixing() ) {
			tmp2rule.instantiate(rule_ctxt.cterm(*sym));
		} else if( auto assm = tmp2rule.assuming() ) {
			tmp2rule.discharge(*condi);
			condi++;
		} else {
			break;
		}
	}
	Thm concl = intro.conclusion().subst(tmp2rule);
	return {*ind,rel,Rule(concl,l,concl.intro(),std::move(conds),cong)};
}

bool Rewrite::register_cong( Thm const& thm ) & {
	auto [ind,rel,cong] = make_rule(thm,true);
	for( auto const& cong : _congs[ind] ) {// do not register duplicates
		if( (Term)cong == thm ) return false;
	}
	_congs[ind].emplace_back(cong);
	return true;
}
void Rewrite::register_fallback( Thm const& thm ) & {
	auto [ind,rel,rule] = make_rule(thm,true);
	_fallbacks.emplace(ind,rule);
}

void Rewrite::register_dual( Thm const& thm ) & {
	Thm thm_strip = strip_all(thm,thm.ctxt().fork(),patvar_maker()).first;
	if( auto const& imp = thm_strip.cbinary(IMP) )
	if( auto const& bin1 = strips_binary(imp->first) )
	if( auto const& ind1 = gets_rel_ind(get<0>(*bin1)) ) {
		CTerm t = imp->second;
		while( auto imp2 = t.cbinary(IMP) ) {
			t = imp2->second;
		}
		if( auto const& bin2 = strips_binary(t) )
		if( auto const& ind2 = gets_rel_ind(get<0>(*bin2)) ) {
			_duals.emplace(*ind2,Dual(thm,*ind1));
			return;
		}
	}
	throw Error("\"malformed dual rule\"")(thm);
}
void Rewrite::register_to_true( Thm const& thm ) & {
	auto rule = Intro::rule(thm);
	auto const& rel = gets_binary_sym(rule.conclusion());
	if( !rel ) throw Error("\"malformed rewrite-to-true\"")(thm);
	auto ind = gets_rel_ind(*rel);
	if( !ind ) throw Error("\"unregistered rewrite relation\"")(*rel)(thm);
	_to_true = {{thm,*ind}};
}
bool Resolver::_step_cond(
	Thy const& thy,// Γ
	Intp& intp,// Γ ⊢ Δ
	CTerm const& cond,// Δ ⊢ φ... ⟹ x = y or ∀v. φ.[v]... ⟹ X.[v] = Y.[v]
	bool rewrite,
	bool simp,
	char ind,
	vector<char>::const_iterator pos_it,
	vector<char>::const_iterator pos_end
) & {
	if( log > 15 ) {
		_log() << "{ rewriting condition (" << rew->_rels[ind] << "): " << thy.pretty(cond) << endl;
	}
	indent++;
	Thy subthy = thy.branch();
	Term pat = cond;// φ... ⟹ x = y or ∀v. φ.[v]... ⟹ X.[v] = Y.[v]
	CTerm source = cond;// unused default
	auto const& all = pat.binder(ALL);
	if( all ) {// pat == ∀v. φ.[v]... ⟹ X.[v] = Y.[v]
		auto v = all->first;
		pat = all->second;// pat == φ.[v]... ⟹ X.[v] = Y.[v]
		auto v2 = avoid(v,[&](auto const& x){ return cond.ctxt().fixes(x) || thy.has_constant(x); });
		auto vt = subthy.fix(v2);// subthy: (Γ; ∀v')
		while( auto imp = pat.binary(IMP) ) {
			auto assm = subthy.assume(subthy.weaken((v /= imp->first).csubst(intp)).inst(vt));
			// assm == ((v. φ.[v])θ).[v'] ≡ φθ.[v']
			inflate(subthy,assm);
			add_intro(subthy,assm);
			pat = imp->second;
		}// subthy == (Γ; ∀v'; φθ.[v']...)
		auto app1 = pat.app();
		assert(app1);
		auto app2 = app1->first.app();
		assert(app2);
		source = subthy.weaken((v /= app2->second).csubst(intp)).inst(vt);// ∀(v. l.[v])θ.[v'] = lθ.[v']
		// source == (Γ; ∀v'; φθ.[v']... ⊢ lθ.[v'])
	} else {// pat: φ... ⟹ x = y
		while( auto imp = pat.binary(IMP) ) {
			auto assm = subthy.assume(subthy.weaken(imp->first.csubst(intp)));// φθ
			inflate(subthy,assm);
			add_intro(subthy,assm);
			pat = imp->second;
		}// subthy == (Γ; φθ...)
		auto app1 = pat.app();
		assert(app1);
		auto app2 = app1->first.app();
		assert(app2);
		source = subthy.weaken(app2->second.csubst(intp));
		// source == (Γ; φθ... ⊢ xθ)
	}
	if( rewrite )
	if( auto o = _step(subthy,source,simp,ind,pos_it,pos_end) ) {
		auto [eq,t] = *o;// Γ; ∀v'; φθ.[v']... ⊢ Xθ.[v'] = t.[v']
		auto res = t.lift(thy.cterm(ALL));// Γ ⊢ ∀v'. t.[v']
		intp.instantiate( all ? res.capp()->second : res );
		intp.discharge(eq.intro());// Γ ⊢ ∀v'. φθ.[v']... ⟹ Xθ.[v'] = res.[v']
		indent--;
		if( log > 14 ) _log() << "} condition rewritten: " << thy.pretty(eq) << endl;
		return true;
	}
	auto eq = _make_refl(subthy,source,ind);
	auto res = source.lift(thy.cterm(ALL));
	intp.instantiate( all ? res.capp()->second : res );
	intp.discharge(eq.intro());
	indent--;
	if( log > 14 ) _log() << "}! condition reflected: " << thy.pretty(eq) << endl;
	return false;
}
Thm Resolver::_make_refl( Thy const& thy, CTerm const& source, char ind ) & {
	indent++;
	Thm refl = thy.weaken(rew->_refls[ind]).instantiate(source);
	while( auto imp = refl.cbinary(IMP) ) {
		refl = refl.discharge(prove(thy,imp->first,false));
	}
	indent--;
	return refl;
}
Opt<Thm> Resolver::_apply_rewrite_rule(
	Thy const& thy,// Γ
	Rewrite::Rule const& rule,// Δ ⊢ ∀x... ∀y. s = y ⟹... l[x...] = r[y...]
	Subst const& matcher,// θ : {x...} → Γ s.t. source == l[x...]θ
	Intp const& rule2thy,// σ : Δ → Γ
	bool simp,
	vector<char>::const_iterator pos_it,
	vector<char>::const_iterator pos_end
) & {
	if( log > 15 ) _log() << "{ applying " << ( rule.cong ? "rewrite" : "congruence" ) << " rule: " << thy.pretty(rule) << endl;
	indent++;
	Ctxt const& rule_ctxt = rule.thm.ctxt();
	Ctxt const& pat_ctxt = rule.pat.ctxt();// (Δ, ∀x..., ∀y, s = y, ...)
	Thy subthy = thy.branch();
	auto intp = Intp::make(pat_ctxt,rule_ctxt).compose(rule2thy).compose(*subthy.parent());
	// Γ ⊢ Δ; intp ? ∀x... ∀y, s = y,...
	for(;;) {// match to left-hand side
		if( auto const& v = intp.fixing() )
		if( auto const& val = matcher.get(*v) ) {
			intp.instantiate(subthy.weaken(*val));
			continue;
		}
		break;
	}
	// Γ ⊢ Δ, ∀x...; θ; ∀y, s = y,...
	size_t i = 0;
	bool applied = false;
	for( auto const& cond : rule.conds ) {
		if( !cond.ind ) {// guard condition should be automatically provable
			auto guard = intp.assuming();
			assert(guard);
			auto o = proves(subthy,*guard,cond.rec);
			if( !o ) {
				indent--;
				if( log > 10 ) _log() << "}! failed to resolve guard: " << thy.pretty(*guard) << endl;
				return {};
			}
			intp.discharge(*o);
		} else {
			if( pos_it == pos_end ) {// active
				applied = _step_cond(subthy,intp,cond.assm,true,simp,*cond.ind,pos_it,pos_end) || applied;
			} else if( *pos_it == i ) {
				applied = _step_cond(subthy,intp,cond.assm,true,simp,*cond.ind,pos_it+1,pos_end) || applied;
			} else {
				_step_cond(subthy,intp,cond.assm,false,false,*cond.ind,pos_it,pos_end);
			}
			i++;
		}
	}
	indent--;
	if( !rule.cong || applied ) {
		if( !intp.ready() ) {
			if( auto const& v = intp.fixing() ) throw Error("\"bad rewrite\"")(rule)("\"unfixed\"")(*v);
			if( auto const& assm = intp.assuming() ) throw Error("\"bad rewrite\"")(rule)("\"undischarged\"")(*assm);
			assert(false);
		}
		auto ret = rule.concl.subst(intp);
		if( log > 12 ) _log() << "} rewritten: " << thy.pretty(ret) << endl;
		return {ret.intro()};
	}
	if( log > 10 ) _log() << "}! failed to rewrite: " << endl;
	return {};
}

Opt<pair<Thm,CTerm>> Resolver::_step( Thy const& thy, CTerm const& source, bool simp, char ind, vector<char>::const_iterator pos_it, vector<char>::const_iterator pos_end ) & {
	if( log > 12 ) {
		_log() << "{ trying to rewrite ";
		if( pos_it != pos_end ) {
			cerr << "[ ";
			for( auto it = pos_it; it != pos_end; it++ ) {
				cerr << (int)*it << ' ';
			}
			cerr << "] ";
		}
		cerr << '(' << rew->_rels[ind] << "): " << thy.pretty(source) << endl;
	}
	indent++;
	auto apply = [&]( Rewrite::Rule const& rule, Subst const& matcher, Intp const& intp )->Opt<Thm> {
		if( auto const& ret = _apply_rewrite_rule(thy,rule,matcher,intp,simp,pos_it,pos_end) ) {
			indent--;
			if( log > 11 ) _log() << "} rewritten: " << thy.pretty(*ret) << endl;
			return ret;
		}
		return {};
	};
	if( pos_it == pos_end ) {// active position
		for( auto const& rule : rules[ind] ) {
			if( log > 13 ) _log() << "- testing explicit rule: " << thy.pretty(rule) << endl;
			if( auto const& m = match(rule.pat,source,is_patvar) )
			if( auto const& ret = apply(rule,*m,thy.interpret_ancestor(rule.thm.ctxt())) ) {
				return {{*ret,ret->capp()->second}};
			}
		}
		if( simp )
		if( auto const& ret = thy.find_thm( Thy::REWRITE+(rew->_rels[ind]), [&]( Import const& import, Thm const& thm, ThmInfo const& info )->Opt<Thm>{
			auto const& rule = info.ref<Rewrite::Rule>();
			assert(rule);
			if( log > 5 ) _log() << "- testing simp rule: " << thy.pretty(thm) << endl;
			if( auto const& m = match(rule->pat,source,is_patvar,{import}) ) {
				return apply(*rule,*m,import);
			}
			return {};
		}) ) {
			return {{*ret,ret->capp()->second}};
		}
	}
	for( auto const& rule : rew->_congs[ind] ) {
		if( auto const& m = match(rule.pat,source,is_patvar) )
		if( auto const& ret = apply(rule,*m,thy.interpret_ancestor(rule.thm.ctxt())) ) {
			return {{*ret,ret->capp()->second}};
		}
	}
	if( auto const& o = rew->_fallbacks.finds(ind) ) {
		auto const& rule = o->second;
		if( auto const& m = match(rule.pat,source,is_patvar) )
		if( auto const& ret = apply(rule,*m,thy.interpret_ancestor(rule.thm.ctxt())) ) {
			return {{*ret,ret->capp()->second}};
		}
	}
	indent--;
	if( log > 10 ) _log() << "}! not rewritten: " << thy.pretty(source) << endl;
	return {};
}

size_t Rewrite::get_ind( Opt<std::string> const& rel ) const & {
	if( rel ) {
		auto const& o = gets_rel_ind(*rel);
		if( !o ) throw Error("\"unregistered relation\"")(*rel);
		return *o;
	} else {
		return _default_ind;
	}
}

Opt<Thm> Resolver::_steps(
	Thy const& thy, 
	CTerm const& s,
	bool simp,
	size_t min,
	size_t max,
	bool normalize,
	vector<char> const& pos,
	char ind
) & {
	auto begin = pos.begin(), end = pos.end();
	auto const& init = _step(thy,s,simp,ind,begin,end);
	if( !init ) {
		if( min == 0 ) {
			return {};
		}
		throw Error("\"rewrite failed\"")(s);
	}
	auto [eq,t] = *init;
	if( max <= 1 && !normalize ) {
		return eq;
	}
	auto const& tranp = rew->_trans.finds(ind);
	if( !tranp ) throw Error("\"transitivity rule unregistered\"");
	// ltrans: ∀y. s = y ⟹ ∀z. y = z ⟹ guards... ⟹ s = z
	Thm ltrans = thy.weaken(tranp->second).instantiate(s);
	if( log > 13 ) _log() << "- applying transitivity: " << thy.pretty(ltrans) << endl;
	for( unsigned int i = 1;; ) {
		auto const& step = _step(thy,t,simp,ind,begin,end);
		if( !step ) {
			if( i < min ) throw Error("\"too few steps\"")(to_string(i))(to_string(min))(t);
			return eq;
		}// t = t2
		auto [eq2,t2] = *step;
		eq = ltrans << eq;// ∀z. t = z ⟹ guards... ⟹ s = z
		eq = eq << eq2;// guards... ⟹ s = t2
		while( auto imp = eq.cbinary(IMP) ) {// discharge guards
			eq = eq.discharge(prove(thy,imp->first,false));
		}
		i++;
		if( i == max ) {
			if( normalize )
				throw Error("\"rewrite limit exceeded\"")(to_string(max));
			return eq;
		}
		t = t2;
	}
}
bool Resolver::rewrites( Thesis& thesis, bool simp, size_t min, size_t max, bool normalize, std::vector<char> const& pos, Opt<std::string> const& rel ) & {
	if( !rew ) return false;
	// thesis: s ⟹ rest
	auto const& goal = thesis.has_goal();
	if( !goal ) return false;
	size_t ind = rew->get_ind(rel);
	auto const& o = rew->_revimps.finds(ind);// ∀x y. x = y ⟹ φ ⟹... y ⟹ x
	if( !o ) throw Error("\"unregistered backward rewriting\"");
	auto const& thy = thesis.thy();
	auto steps = _steps(thy,*goal,simp,min,max,normalize,pos,ind);// s = t
	bool ret = steps;
	if( ret ) {
		auto imp = thy.weaken(o->second.thm);// x = y ⟹ φ ⟹... y ⟹ x
		imp = imp << *steps; // φθ ⟹... t ⟹ s
		auto conds = o->second.conds;
		for( size_t i = 0; i < conds; i++ ) {
			imp = imp.discharge(prove(thy,imp.cbinary(IMP)->first,false));
		}// t ⟹ s
		thesis.apply(Intro::imp(imp,1,false));// t ⟹ rest
	}
	if( thesis.push() ) {
		if( rewrites(thesis,simp,0,max,normalize,pos,rel) ) {
			ret = true;
		}
		thesis.pop();
	}
	if( log > 1 ) _log() << "rewritten thesis to: " << thesis << endl;
	return ret;
}
Thm Resolver::rewrites( Thy const& thy, Thm const& source, bool simp, size_t min, size_t max, bool normalize, std::vector<char> const& pos ) & {
	size_t ind = rew->_default_ind;
	auto const& o = rew->_imps.finds(ind);
	if( !o ) throw Error("\"unregistered forward rewriting\"");
	auto steps = _steps(thy,source,simp,min,max,normalize,pos,ind);
	if( !steps ) {
		return source;
	}
	auto tmp = thy.weaken(o->second.thm);// (s ⟺ t) ⟹ conds... ⟹ s ⟹ t
	tmp = tmp << *steps;// conds... ⟹ s ⟹ t
	for( int i = 0; i < o->second.conds; i++ ) {
		tmp = discharge(thy,tmp,false);
	}// s ⟹ t
	return tmp << source;
}
void Rewrite::import( Thy const& thy, Intp const& intp ) & {
	int i = 0;
	auto const& src = *thy.rewriter();
	for( auto const& refl : src._refls ) {
		register_refl(thy.weaken(refl).subst(intp),i==src._default_ind);
		i++;
	}
	for( auto const& congs : src._congs ) {
		for( auto const& cong : congs ) {
			register_cong(thy.weaken(cong).subst(intp));
		}
	}
	for( auto const& [i,dual] : src._duals ) {
		register_dual(thy.weaken(dual.thm).subst(intp));
	}
	for( auto const& [i,trans] : src._trans ) {
		register_trans(thy.weaken(trans).subst(intp));
	}
	for( auto const& [i,imp] : src._imps ) {
		register_imp(thy.weaken(imp.thm).subst(intp),true);
	}
	for( auto const& [i,imp] : src._revimps ) {
		register_imp(thy.weaken(imp.thm).subst(intp),false);
	}
	if( auto const& to_true = src._to_true ) {
		register_to_true(thy.weaken(to_true->first).subst(intp));
	}
}
