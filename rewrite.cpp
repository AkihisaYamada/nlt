#include <iostream>
#include "inference.hpp"

using namespace std;

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

Thm Thy::dualize( Thm const& thm, Resolver& resolver ) & {
	Thy subthy = branch();
	Thm body = subthy.weaken(thm);
	for(;;) {
		body = strip_all(body,subthy).first;
		auto imp = body.cbinary(IMP);
		if(!imp) break;
		Thm assm = subthy.assume(imp->first);
		add_intro(subthy,assm);
		body = body.impE(assm);
	}
	if( auto const& bin = strips_binary(body) ) {
		auto const& [rel,l,r] = *bin;
		auto const& [dual,info] = term_thm(rel,DUAL);
		Thm dual_thm = subthy.weaken(dual) << body;
		while( auto o = resolver.discharges(subthy,dual_thm,{}) ) {
			dual_thm = *o;
		}
		return dual_thm.intro();
	}
	throw Error("\"not dualizable\"")(body);
}

void Rewrite::add_rewrite_rule( Rewrite::Rules& rules, Thm const& thm, bool cong ) const & {
	auto const& [ind,rel,rule] = make_rule(thm,cong);
	rules[ind].emplace_back(std::move(rule));
}

void Thy::register_imp( Thm const& thm, bool dir ) & {
	auto var_ctxt = thm.ctxt().fork().ctxt();
	auto rule = strip_all(var_ctxt.weaken(thm),var_ctxt,patvar_maker()).first;// x = y ⟹ conds... ⟹ x ⟹ y
	if( auto const& imp = rule.cbinary(IMP) )
	if( auto const& bin = strips_binary(imp->first) )
	if( auto const& imp2 = imp->second.cbinary(IMP) ) {// conds... ⟹ x ⟹ y
		auto const& [rel,l,r] = *bin;
		Term t = imp2->second;
		size_t conds = 0;
		while( auto imp3 = t.binary(IMP) ) {
			t = imp3->second;
			conds++;
		}
		add_term_thm( rel, dir ? REWRITE_IMP : REWRITE_REV, thm, Rewrite::ImpInfo{conds} );
		return;
	}
	throw Error("\"malformed imp\"")(thm);
}
bool Rewrite::register_rel( string const& rel, bool def ) & {
	if( !gets_rel_ind(rel) ) {
		size_t ind = _rels.size();
		_rels.emplace_back(rel);
		_rel2ind.emplace(rel,ind);
		_congs.emplace_back();
	}
	if( def ) {
		_default_rel = {rel};
	}
	return true;
}
void Thy::register_refl( Thm const& thm ) & {
	auto rule = Intro::rule(thm);
	auto const& rel = gets_binary_sym(rule.conclusion());
	if( !rel ) throw Error("\"malformed refl\"")(thm);
	add_term_thm(*rel,REFL,thm);
}
void Thy::register_trans( Thm const& thm ) & {
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
	if( *rel1 == *rel2 && *rel2 == *rel3 ) {
		add_term_thm(*rel1,TRANS,thm);
		return;
	}
	throw Error("\"malformed trans\"")(thm);
}
Thm Thy::trans( Term const& rel ) & {
	return term_thm(rel,TRANS).first;
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
						auto constraint = cond_ctxt.closed(s);
						if( !constraint ) throw Error("\"open constrained condition or guard\"")(body)(thm);
						cond_ctxt.assume(*constraint);
						body = t;
						continue;
					}
					if( auto ind = gets_rel_ind(rel) ) {// rewrite condition
						auto cond_lhs = cond_ctxt.closed(s);
						if( !cond_lhs ) throw Error("\"open condition lhs\"")(s)(thm);
						auto cond = rule_ctxt.assume((Term)*assm);//TODO: reduce double-check
						if( abs && !t.unbind() ) throw Error("\"unsupported condition\"")(t)(thm);
						conds.emplace_back(rel,abs,true,cond);
						cond_thms.emplace_back(std::move(cond));
						break;
					}
				}
				// guard
				auto cond_conc = cond_ctxt.closed(body);
				if( !cond_conc ) throw Error("\"open guard\"")(body)(thm);
				auto cond = rule_ctxt.assume(cond_conc->intro());
				conds.emplace_back(Opt<string>{},false,(bool)body.sym(),cond);
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

void Thy::register_dual( Thm const& thm ) & {
	auto var_ctxt = thm.ctxt().fork().ctxt();
	Thm thm_strip = strip_all(var_ctxt.weaken(thm),var_ctxt,patvar_maker()).first;
	if( auto const& imp = thm_strip.cbinary(IMP) )
	if( auto const& bin = strips_binary(imp->first) ) {
		auto const& [rel,l,r] = *bin;
		CTerm t = imp->second;
		while( auto imp2 = t.cbinary(IMP) ) {
			t = imp2->second;
		}
		add_term_thm(rel,DUAL,thm);
		return;
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
	Opt<std::string const&> simp,
	string const& rel,
	vector<char>::const_iterator pos_it,
	vector<char>::const_iterator pos_end
) & {
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
	if( auto o = _step(subthy,source,simp,rel,pos_it,pos_end) ) {
		auto [eq,t] = *o;// Γ; ∀v'; φθ.[v']... ⊢ Xθ.[v'] = t.[v']
		auto res = t.lift();// Γ ⊢ ∀v'. t.[v']
		intp.instantiate( all ? res.capp()->second : res );
		intp.discharge(eq.intro());// Γ ⊢ ∀v'. φθ.[v']... ⟹ Xθ.[v'] = res.[v']
		return true;
	}
	auto eq = _make_refl(subthy,source,rel);
	auto res = source.lift();
	intp.instantiate( all ? res.capp()->second : res );
	intp.discharge(eq.intro());
	if( log > 14 ) _log() << "! condition reflected: " << thy.pretty(eq) << endl;
	return false;
}
Thm Resolver::_make_refl( Thy& thy, CTerm const& source, string const& rel ) & {
	indent++;
	Thm refl = thy.term_thm(rel,REFL).first.allE(source);
	while( auto imp = refl.cbinary(IMP) ) {
		refl = refl.impE(prove(thy,imp->first,{}));
	}
	indent--;
	return refl;
}
Opt<Thm> Resolver::_apply_rewrite_rule(
	Thy const& thy,// Γ
	Rewrite::Rule const& rule,// Δ ⊢ ∀x... ∀y. s = y ⟹... l[x...] = r[y...]
	Subst const& matcher,// θ : {x...} → Γ s.t. source == l[x...]θ
	Intp const& rule2thy,// σ : Δ → Γ
	Opt<std::string const&> simp,
	vector<char>::const_iterator pos_it,
	vector<char>::const_iterator pos_end
) & {
	if( log > 12 ) _log() << "{ " << ( rule.cong ? "cong" : "rewrite" ) << " rule " << "matched: " << thy.pretty(rule.thm) << endl;
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
		if( !cond.rel ) {// guard condition should be automatically provable
			auto guard = intp.assuming();
			assert(guard);
			auto o = proves( subthy, *guard, cond.rec ? simp : Opt<string const&>{} );
			if( !o ) {
				indent--;
				if( log > 10 ) _log() << "}! failed to resolve guard: " << thy.pretty(*guard) << endl;
				return {};
			}
			intp.discharge(*o);
		} else {
			if( pos_it == pos_end ) {// active
				applied = _step_cond(subthy,intp,cond.assm,true,simp,*cond.rel,pos_it,pos_end) || applied;
			} else if( *pos_it == i ) {
				applied = _step_cond(subthy,intp,cond.assm,true,simp,*cond.rel,pos_it+1,pos_end) || applied;
			} else {
				_step_cond(subthy,intp,cond.assm,false,{},*cond.rel,pos_it,pos_end);
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
	if( log > 13 ) _log() << "}! failed to apply: " << thy.pretty(rule) << endl;
	return {};
}

Opt<pair<Thm,CTerm>> Resolver::_step( Thy const& thy, CTerm const& source, Opt<std::string const&> simp, string const& rel, vector<char>::const_iterator pos_it, vector<char>::const_iterator pos_end ) & {
	size_t ind = rew->gets_rel_ind(rel).value_or_throw(Error("\"Unregistered rewrite relation\"")(rel));
	if( log > 12 ) {
		_log() << "- rewriting ";
		if( pos_it != pos_end ) {
			cerr << "[at ";
			for( auto it = pos_it; it != pos_end; it++ ) {
				cerr << (int)*it << ' ';
			}
			cerr << "] ";
		}
		cerr << '(' << rel << "): " << thy.pretty(source) << endl;
	}
	indent++;
	auto apply = [&]( Rewrite::Rule const& rule, Subst const& matcher, Intp const& intp )->Opt<Thm> {
		if( auto const& ret = _apply_rewrite_rule(thy,rule,matcher,intp,simp,pos_it,pos_end) ) {
			indent--;
			if( log > 19 ) _log() << "* rewritten: " << thy.pretty(*ret) << endl;
			return ret;
		}
		return {};
	};
	if( pos_it == pos_end ) {// active position
		for( auto const& rule : rules[ind] ) {
			if( auto const& m = match(rule.pat,source,is_patvar) ) {
				if( auto const& ret = apply(rule,*m,thy.interpret_ancestor(rule.thm.ctxt())) ) {
					return {{*ret,ret->capp()->second}};
				}
			} else {
				if( log > 15 ) _log() << "! explicit rule didn't match: " << thy.pretty(rule) << endl;
			}
		}
		if( simp )
		if( auto const& ret = thy.find_thm( *simp + rew->_rels[ind], [&]( Import const& import, string_view const&, Thm const& thm, ThmInfo const& info )->Opt<Thm>{
			auto const& rule = info.ref<Rewrite::Rule>();
			assert(rule);
			if( auto const& m = match(rule->pat,source,is_patvar,{import}) ) {
				return apply(*rule,*m,import);
			} else {
				if( log > 15 ) _log() << "! simp rule didn't match: " << thy.pretty(thm) << endl;
			}
			return {};
		}) ) {
			return {{*ret,ret->capp()->second}};
		}
	}
	for( auto const& rule : rew->_congs[ind] ) {
		if( auto const& m = match(rule.pat,source,is_patvar) ) {
			if( auto const& ret = apply(rule,*m,thy.interpret_ancestor(rule.thm.ctxt())) ) {
				return {{*ret,ret->capp()->second}};
			}
		} else {
			if( log > 15 ) _log() << "! cong rule didn't match: " << thy.pretty(rule) << endl;
		}
	}
	if( auto const& rule = rew->_fallbacks.finds_value(ind) ) {
		if( auto const& m = match(rule->pat,source,is_patvar) ) {
			if( auto const& ret = apply(*rule,*m,thy.interpret_ancestor(rule->thm.ctxt())) ) {
				return {{*ret,ret->capp()->second}};
			}
		} else {
			if( log > 15 ) _log() << "- testing fall-back rule: " << thy.pretty(*rule) << endl;
		}
	}
	indent--;
	if( log > 19 ) _log() << "! not rewritten: " << thy.pretty(source) << endl;
	return {};
}

size_t Rewrite::get_ind( Opt<std::string> const& rel ) const & {
	return gets_rel_ind(rel.value_or(default_rel())).value_or_throw( Error("\"unregistered relation\"")(*rel) );
}

Opt<Thm> Resolver::_steps(
	Thy& thy, 
	CTerm const& s,
	Opt<std::string const&> simp,
	size_t min,
	size_t max,
	bool normalize,
	vector<char> const& pos,
	string const& rel
) & {
	auto begin = pos.begin(), end = pos.end();
	auto const& init = _step(thy,s,simp,rel,begin,end);
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
	auto trans = thy.term_thm(rel,TRANS).first;
	// ltrans: ∀y. s = y ⟹ ∀z. y = z ⟹ guards... ⟹ s = z
	Thm ltrans = trans.allE(s);
	if( log > 13 ) _log() << "- applying transitivity: " << thy.pretty(ltrans) << endl;
	for( unsigned int i = 1;; ) {
		auto const& step = _step(thy,t,simp,rel,begin,end);
		if( !step ) {
			if( i < min ) throw Error("\"too few steps\"")(to_string(i))(to_string(min))(t);
			return eq;
		}// t = t2
		auto [eq2,t2] = *step;
		eq = ltrans << eq;// ∀z. t = z ⟹ guards... ⟹ s = z
		eq = eq << eq2;// guards... ⟹ s = t2
		while( auto imp = eq.cbinary(IMP) ) {// discharge guards
			eq = eq.impE(prove(thy,imp->first,{}));
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
bool Resolver::rewrites( Thesis& thesis, Opt<std::string const&> simp, size_t min, size_t max, bool normalize, bool wide, std::vector<char> const& pos, Opt<std::string const&> orel ) & {
	if( !rew ) return false;
	// thesis: s ⟹ rest
	auto const& goal = thesis.has_goal();
	if( !goal ) return false;
	auto& thy = thesis.thy();
	auto const& rel = orel.value_or(rew->default_rel());
	auto const& [revimp,info] = thy.term_thm(rel,REWRITE_REV);
	auto const& impinfo = *ASSERTED(info.ref<Rewrite::ImpInfo>());
	auto steps = _steps(thy,*goal,simp,min,max,normalize,pos,rel);// s = t
	auto ret = (bool)steps;
	if( ret ) {
		auto imp = revimp;// ∀x y. x = y ⟹ φ ⟹... y ⟹ x
		imp = imp << *steps; // φθ ⟹... t ⟹ s
		for( size_t i = 0; i < impinfo.conds; i++ ) {
			imp = imp.impE(prove(thy,imp.cbinary(IMP)->first,{}));
		}// t ⟹ s
		thesis.apply(Intro::imp(imp,1,false),false);// t ⟹ rest
	}
	if( wide && thesis.push() ) {
		if( rewrites(thesis,simp,0,max,normalize,wide,pos,rel) ) {
			ret = true;
		}
		thesis.pop();
	}
	if( log > 1 ) _log() << "rewritten thesis to: " << thesis << endl;
	return ret;
}
Thm Resolver::rewrites( Thy& thy, Thm const& source, Opt<std::string const&> simp, size_t min, size_t max, bool normalize, std::vector<char> const& pos ) & {
	string rel = rew->_default_rel.value_or_throw(Error("\"no default rewrite relation\""));
	auto const& [imp,info] = thy.term_thm(rel,REWRITE_IMP);
	auto const& impinfo = *ASSERTED(info.ref<Rewrite::ImpInfo>());
	auto tmp = imp; // ∀x y. (x ⟺ y) ⟹ conds... ⟹ x ⟹ y
	auto steps = _steps(thy,source,simp,min,max,normalize,pos,rel);
	if( !steps ) {
		return source;
	}
	tmp = tmp << *steps;// conds... ⟹ s ⟹ t
	for( int i = 0; i < impinfo.conds; i++ ) {
		tmp = discharge(thy,tmp,{});
	}// s ⟹ t
	return tmp << source;
}
void Rewrite::import( Rewrite const& src, Thy const& thy, Intp const& intp, bool override_default ) & {
	override_default = override_default || !_default_rel;
	for( auto const& rel : src._rels ) {
		register_rel( rel, override_default && src._default_rel.contains(rel) );
	}
	for( auto const& congs : src._congs ) {
		for( auto const& cong : congs ) {
			register_cong(thy.weaken(cong).subst(intp));
		}
	}
	for( auto const& [i,thm] : src._fallbacks ) {
		register_fallback(thy.weaken(thm).subst(intp));
	}
	if( auto const& to_true = src._to_true ) {
		register_to_true(thy.weaken(to_true->first).subst(intp));
	}
}
