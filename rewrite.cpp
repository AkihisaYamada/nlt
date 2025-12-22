#include <iostream>
#include "inference.hpp"

using namespace std;

string const Rewrite::CONG = "#cong";
Rewrite::Ctrl const Rewrite::DEFAULT_CTRL = {};

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

Thm Thy::dualize( Thm const& thm ) const & {
	Thy subthy = branch();
	Thm body = strip_all(thm,*subthy.parent()).first;
	while( auto imp = body.cbinary(IMP) ) {
		Thm assm = subthy.assume(imp->first);
		add_forced(subthy,assm);
		body = body.discharge(assm);
	}
	if( auto const& bin = strips_binary(body) )
	if( auto const& ind = rewriter()->gets_rel_ind(get<0>(*bin)) ) {
		auto const& dual = rewriter()->_duals.finds(*ind);
		if( !dual ) throw Error("\"no dual rule for\"")(get<0>(*bin));
		Thm dual_thm = subthy.weaken(dual->second.thm) << body;
		auto inf = Blaster(subthy.rewriter());
		while( auto o = inf.blasts(subthy,dual_thm,false) ) {
			dual_thm = *o;
		}
		return dual_thm.intro();
	}
	throw Error("\"not dualizable\"")(thm);
}

void Thy::add_rewrite_rule( Rewrite::Rules& rules, Thm const& thm ) const & {
	auto const& [ind,rule] = rewriter()->make_cong(thm);
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
	if( auto const& imp1 = strip_all(thm,thm.ctxt().fork(),patvar_maker()).first.cbinary(IMP) )
	if( auto const& imp2 = imp1->second.cbinary(IMP) )
	if( auto const& rel = gets_binary_sym(imp1->first) ) {
		auto const& ind = gets_rel_ind(*rel);
		if( !ind ) throw Error("\"unregistered relation\"")(*rel);
		_trans.emplace(*ind,thm);
		return;
	}
	throw Error("\"malformed trans\"")(thm);
}
pair<char,Rewrite::Cong> Rewrite::make_cong( Thm const& thm ) const& {
	// parsing congruence rule
	auto rule = Intro::rule(thm);// fix x... y... x = y ..., φ... ⊢ l[x...] = r[y...]
	Ctxt ctxt = rule.conclusion().ctxt();
	vector<Cong::Cond> conds;
	size_t rev = 0;
	while( ctxt.fixed(rev) ) rev++;
	while( auto assm = ctxt.assumed(rev) ) {
		Term body = *assm;
		bool abs;
		if( auto all = body.binder(ALL) ) {
			body = all->second;
			abs = true;
		} else {
			abs = false;
		}
		auto ind = Opt<size_t>{};
		while( auto x = strips_binary(body) ) {
			auto const* rel = &get<0>(*x);
			if( *rel == IMP ) {// guarded condition
				body = get<2>(*x);
				continue;
			}
			ind = gets_rel_ind(*rel);
			break;
		}
		bool rec = ind || body.sym();
		conds.emplace_back( ind, abs, rec, abs ? assm->capp()->second : *assm );
		rev++;
	}
	if( auto const& bin = strips_binary(rule.conclusion()) ) {
		auto const& [rel,l,r] = *bin;
		if( auto const& ind = gets_rel_ind(rel) ) {
			return {*ind,Cong(rule.conclusion(),l,thm,std::move(conds))};
		}
	}
	// The conclusion is not a rewrite relation.
	throw Error("\"malformed rewrite rule\"")(thm);
}

bool Rewrite::register_cong( Thm const& thm ) & {
	auto [ind,cong] = make_cong(thm);
	for( auto const& cong : _congs[ind] ) {// do not register duplicates
		if( (Term)cong == thm ) return false;
	}
	_congs[ind].emplace_back(cong);
	return true;
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

pair<Thm,bool> Blaster::_step_abs( Thy const& thy, CTerm const& source, char ind, CTerm const& goalpat, Subst const& subst, bool rewrite ) & {
	if( log > 4 ) {
		_log() << "+ trying to rewrite binding (" << rew->_rels[ind] << "): " << thy.pretty(source) << endl;
	}
	indent++;
	auto const& abs = source.bind();
	assert(abs);
	Thy subthy = thy.branch();
	CTerm v = subthy.fix(avoid(abs->first,[&](auto const& v){ return thy.has_constant(v); }));
	CTerm body = subthy.weaken(source).inst(v);
	Term goal = goalpat.Term::inst(subthy.cterm(abs->first)).subst(subst);
	while( auto imp = goal.binary(IMP) ) {
		auto assm = subthy.assume(imp->first);
		inflate(subthy,assm);
		add_forced(subthy,assm);
		goal = imp->second;
	}
	indent--;
	if( rewrite )
	if( auto const& eq = _step(subthy,body,ind) ) {
		if( log > 3 ) {
			_log() << "* rewritten: " << thy.pretty(*eq) << endl;
		}
		return {eq->intro(),true};
	}
	if( log > 4 ) {
		_log() << "! not rewritten binding: " << thy.pretty(source) << endl;
	}
	return {_make_refl(subthy,body,ind).intro(),false};
}
Thm Blaster::_make_refl( Thy const& thy, CTerm const& source, char ind ) & {
	Thm refl = thy.weaken(rew->_refls[ind]).instantiate(source);
	while( auto imp = refl.cbinary(IMP) ) {
		refl = refl.discharge(prove(thy,imp->first,false));
	}
	return refl;
}
Opt<Thm> Blaster::_apply_cond_rewrite( Thy const& thy, Rewrite::Cong const& rule, Subst const& matcher, bool success ) & {
	if( log > 4 ) _log() << "- applying conditional rule: " << thy.pretty(rule) << endl;
	Ctxt const& rule_ctxt = rule.thm.ctxt();
	Ctxt const& pat_ctxt = rule.pat.ctxt();
	Thy subthy = thy.branch();
	auto intp = Intp::make(pat_ctxt,rule_ctxt).compose(subthy.interpret_ancestor(rule_ctxt));
	for(;;) {
		if( auto const& v = intp.fixing() ) {
			if( auto const& val = matcher.get(*v) ) {
				intp.instantiate(subthy.weaken(*val));
			} else {
				intp.instantiate(subthy.fix(avoid(*v,[&](auto x){ return subthy.fixes(x); })));
			}
		} else if( auto const& assm = intp.assuming() ) {// TODO: improve
			intp.discharge(subthy.assume(*assm));
		} else {
			break;
		}
	}
	Thm ret = rule.concl.subst(intp).intro();
	// ret: ∀y.... (φ ⟹ x = y) ⟹ ... ⟹ lθ = C[y...]
	// TODO: instantiate x...
	size_t i = 0;
	for( auto const& cond : rule.conds ) {
		if( !cond.ind ) {// guard condition should be automatically provable
			if( auto o = blasts(thy,ret,cond.rec) ) {
				ret = *o;
			} else {
				if( log > 0 ) _log() << "! failed to resolve cong guard: " << thy.pretty(cond.assm) << endl;
				return {};
			}
		} else {
			auto v = pat_ctxt.fixed(i);
			assert(v);
			i++;
			auto const& si = matcher.get(*v);
			if( !si ) throw Error("\"unexpected cong rule\"")(rule);
			if( cond.abs ) {
				auto [eq,suc] = _step_abs(thy,*si,*cond.ind,cond.assm,matcher,true);
				ret = match_discharge(ret,eq);
				success = success || suc;
			} else if( auto eq = _step(thy,*si,*cond.ind) ) {
				ret = match_discharge(ret,*eq);
				success = true;
				continue;
			} else {
				ret = ret << _make_refl(thy,*si,*cond.ind);
			}
		}
	}
	if( success ) {
		return {ret};
	}
	return {};
}

Opt<Thm> Blaster::_step( Thy const& thy, CTerm const& source, char ind ) & {
	if( log > 4 ) {
		_log() << "+ trying to rewrite (" << rew->_rels[ind] << "): " << thy.pretty(source) << endl;
	}
	indent++;
	for( auto const& rule : rules[ind] ) {
		if( log > 5 ) _log() << "- testing rewrite rule: " << thy.pretty(rule) << endl;
		if( auto const& m = match(rule.pat,source,is_patvar) )
		if( auto const& ret = _apply_cond_rewrite(thy,rule,*m,true) ) {
			indent--;
			if( log > 3 ) _log() << "* rewritten: " << thy.pretty(*ret) << endl;
			return ret;
		}
	}
	if( auto ret = thy.find_thm( Thy::REWRITE+ind, [&]( Import const& import, Thm const& thm, ThmInfo const& info )->Opt<Thm>{
		auto const& rule = info.ref<Rewrite::Cong>();
		assert(rule);
		if( log > 5 ) _log() << "testing rewrite rule: " << thy.pretty(thm) << endl;
		if( auto const& m = match(rule->pat,source,is_patvar,{import}) )
			return _apply_cond_rewrite(thy,*rule,*m,true);
		return {};
	}) ) {
		indent--;
		if( log > 3 ) _log() << "* rewritten: " << thy.pretty(*ret) << endl;
		return ret;
	}
	for( auto const& cong : rew->_congs[ind] ) {
		if( auto const& m = match(cong.pat,source,is_patvar) ) {// source: C[s...]
			if( auto ret = _apply_cond_rewrite(thy,cong,*m,false) ) {
				indent--;
				if( log > 3 ) _log() << "* rewritten: " << thy.pretty(*ret) << endl;
				return ret;
			}
			break;
		}
	}
	indent--;
	if( log > 4 ) _log() << "! not rewritten: " << thy.pretty(source) << endl;
	return {};
}

pair<Thm,bool> Blaster::_step_abs( Thy const& thy, CTerm const& source, char ind, vector<char>::const_iterator pos_it, vector<char>::const_iterator pos_end, bool rewrite ) & {
	if( log > 4 ) {
		_log() << "+ trying to rewrite in binding (" << rew->_rels[ind] << "): " << thy.pretty(source) << endl;
	}
	indent++;
	auto const& abs = source.bind();
	assert(abs);
	Thy subthy = thy.branch();
	CTerm v = subthy.fix(avoid(abs->first,[&](auto const& v){ return thy.has_constant(v); }));
	CTerm body = subthy.weaken(source).inst(v);
	if( auto const& eq = _step(subthy,body,ind,pos_it,pos_end) ) {
		indent--;
		return {eq->intro(),true};
	}
	indent--;
	return {_make_refl(subthy,body,ind).intro(),false};
}

Opt<Thm> Blaster::_step( Thy const& thy, CTerm const& source, char ind, vector<char>::const_iterator pos_it, vector<char>::const_iterator pos_end ) & {
	if( pos_it == pos_end ) {// rewritable position
		return _step(thy,source,ind);
	}
	for( auto const& cong : rew->_congs[ind] ) {
		auto const& pat_ctxt = cong.pat.ctxt();// C[x...]
		if( auto const& m = match(cong.pat,source,is_patvar) ) {// source: C[s...]
			Thm ret = thy.weaken(cong);// ret: ∀x. ∀y. x = y ⟹ ... ⟹ C[x...] = C[y...]
			size_t i = 0;
			for( auto const& cond : cong.conds ) {
				if( !cond.ind ) {// guard condition is assumed to be automatically provable
					ret = blast(thy,ret,false);
				} else {
					auto const& si = m->get(*pat_ctxt.fixed(i));
					assert(si);
					if( *pos_it == i ) {// rewrite step must occur inside this position
						pos_it++;
						if( cond.abs ) {
							auto [eq,suc] = _step_abs(thy,*si,*cond.ind,pos_it,pos_end,true);
							if( !suc ) return {};
							ret = ret << eq;
						} else {
							auto const& eq = _step(thy,*si,*cond.ind,pos_it,pos_end);
							if( !eq ) return {};// no rewrite step was done
							ret = ret << *eq;// rewrite step was successful
						}
					} else {
						if( cond.abs ) {
							auto [eq,suc] = _step_abs(thy,*si,*cond.ind,pos_it,pos_end,false);
							ret = ret << eq;
						} else {
							ret = ret << _make_refl(thy,*si,*cond.ind);
						}
					}
					i++;
				}
			}
			return ret;
		}
	}
	return {};
}

size_t Rewrite::_get_ind( Opt<std::string> const& rel ) const {
	if( rel ) {
		auto const& o = gets_rel_ind(*rel);
		if( !o ) throw Error("\"unregistered relation\"")(*rel);
		return *o;
	} else {
		return _default_ind;
	}
}

Opt<Thm> Blaster::_steps(
	Thy const& thy, 
	CTerm const& s,
	size_t min,
	size_t max,
	bool safe,
	vector<char> const& pos,
	char ind
) & {
	auto begin = pos.begin(), end = pos.end();
	auto const& init = _step(thy,s,ind,begin,end);
	if( !init ) {
		if( min == 0 ) {
			return {};
		}
		throw Error("\"rewrite failed\"")(s);
	}
	Thm eq = *init;
	if( max <= 1 && safe ) {
		return eq;
	}
	auto const& tranp = rew->_trans.finds(ind);
	if( !tranp ) throw Error("\"transitivity rule unregistered\"");
	// ltrans: ∀y z. s = y ⟹ y = z ⟹ types... ⟹ s = z
	Thm ltrans = thy.weaken(tranp->second).instantiate(s);
	assert(eq.app());
	CTerm t = eq.capp()->second;
	for( unsigned int i = 1;; ) {
		auto const& step = _step(thy,t,ind,begin,end);
		if( !step ) {
			if( i < min ) throw Error("\"too few steps\"")(to_string(i))(to_string(min))(t);
			return eq;
		}// t = u
		auto const& app = step->capp();
		assert(app);
		eq = ltrans << eq;// ∀z. t = z ⟹ types... ⟹ s = z
		eq = eq << *step;// types... ⟹ s = u
		while( auto imp = eq.cbinary(IMP) ) {// discharge types
			eq = eq.discharge(prove(thy,imp->first,false));
		}
		i++;
		if( i == max ) {
			if( !safe )
				throw Error("\"rewrite limit exceeded\"")(to_string(max));
			return eq;
		}
		t = app->second;
	}
}
bool Blaster::rewrites( Thesis& thesis, bool failable ) & {
	if( !rew ) return false;
	// thesis: s ⟹ rest
	auto const& goal = thesis.has_goal();
	if( !goal ) return false;
	size_t ind = rew->_get_ind(ctrl.rel);
	auto const& o = rew->_revimps.finds(ind);// ∀x y. x = y ⟹ conds... ⟹ y ⟹ x
	if( !o ) throw Error("\"unregistered backward rewriting\"");
	auto const& thy = thesis.thy();
	auto steps = _steps( thy, *goal, failable ? 0 : ctrl.min, ctrl.max, ctrl.safe, ctrl.pos, ind );// s = t
	if( !steps ) return false;
	auto imp = thy.weaken(o->second.thm);// x = y ⟹ conds... ⟹ y ⟹ x
	imp = imp << *steps; // conditions... ⟹ t ⟹ s
	auto conds = o->second.conds;
	thesis.apply(Intro::imp(imp,conds+1));// conditions... ⟹ t ⟹ rest
	for( size_t i = 0; i < conds; i++ ) {
		blast(thesis,false);
	}// t ⟹ s
	return true;
}
Thm Blaster::rewrites( Thy const& thy, Thm const& source, size_t min ) & {
	size_t ind = rew->_get_ind(ctrl.rel);
	auto const& o = rew->_imps.finds(ind);
	if( !o ) throw Error("\"unregistered forward rewriting\"");
	auto steps = _steps(thy,source,min,ctrl.max,ctrl.safe,ctrl.pos,ind);
	if( !steps ) {
		return source;
	}
	auto tmp = thy.weaken(o->second.thm);// (s ⟺ t) ⟹ conds... ⟹ s ⟹ t
	tmp = tmp << *steps;// conds... ⟹ s ⟹ t
	for( int i = 0; i < o->second.conds; i++ ) {
		tmp = blast(thy,tmp,false);
	}// s ⟹ t
	return tmp << source;
}
void Rewrite::import( Thy const& thy, Intp const& intp ) & {
	int i = 0;
	for( auto const& refl : thy.rewriter()->_refls ) {
		register_refl(thy.weaken(refl).subst(intp),i==_default_ind);
		i++;
	}
	for( auto const& congs : thy.rewriter()->_congs ) {
		for( auto const& cong : congs ) {
			register_cong(thy.weaken(cong).subst(intp));
		}
	}
	for( auto const& [i,dual] : thy.rewriter()->_duals ) {
		register_dual(thy.weaken(dual.thm).subst(intp));
	}
	for( auto const& [i,trans] : thy.rewriter()->_trans ) {
		register_trans(thy.weaken(trans).subst(intp));
	}
	for( auto const& [i,imp] : thy.rewriter()->_imps ) {
		register_imp(thy.weaken(imp.thm).subst(intp),true);
	}
	for( auto const& [i,imp] : thy.rewriter()->_revimps ) {
		register_imp(thy.weaken(imp.thm).subst(intp),false);
	}
	if( auto const& to_true = thy.rewriter()->_to_true ) {
		register_to_true(thy.weaken(to_true->first).subst(intp));
	}
}
