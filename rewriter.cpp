#include <iostream>
#include "inference.hpp"

using namespace std;

string const Rewriter::CONG = "#cong";

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

void Rewriter::add_rule( Thy const& thy, Rules& rules, Thm const& thm, bool rev ) const {
	// checking well-formedness and extracting the lhs of the rewrite rule
	Thy subthy = thy.branch();
	Thm body = strip_all(thm,*subthy.parent(),fresh_maker()).first;
	while( auto imp = body.cbinary(IMP) ) {
		Thm assm = subthy.assume(imp->first);
		add_forced(subthy,assm);
		body = body.discharge(assm);
	}
	if( auto const& bin = strips_binary(body) )
	if( auto const& ind = gets_rel_ind(get<0>(*bin)) ) {
		if( rev ) {
			auto const& dual = _duals.finds(*ind);
			if( !dual ) throw Error("\"no dual rule registered\"");
			Thm dual_thm = subthy.weaken(dual->second.thm) << body;
			while( auto o = blasts(dual_thm,subthy) ) {
				dual_thm = *o;
			}
			rules[dual->second.ind].emplace_back(get<2>(*bin),dual_thm,thm.ctxt());
		} else {
			rules[*ind].emplace_back(get<1>(*bin),body,thm.ctxt());
		}
		return;
	}
	throw Error("\"malformed rule\"")(thm);
}
Rewriter& Rewriter::register_imp( Thm const& thm, bool dir ) & {
	auto rule = strip_all(thm,thm.ctxt().fork(),fresh_maker()).first;// x = y ⟹ conds... ⟹ x ⟹ y
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
		return *this;
	}
	throw Error("\"malformed imp\"")(thm);
}
Rewriter& Rewriter::register_refl( Thm const& thm, bool def ) & {
	auto rule = Intro::rule(thm);
	auto const& rel = gets_binary_sym(rule.conclusion());
	if( !rel ) throw Error("\"malformed refl\"")(thm);
	size_t ind = _rels.size();
	_rels.emplace(*rel,ind);
	_refls.emplace_back(thm);
	_congs.emplace_back();
	if( def ) {
		_default_ind = ind;
	}
	return *this;
}
Rewriter& Rewriter::register_trans( Thm const& thm ) & {
	if( auto const& imp1 = strip_all(thm,thm.ctxt().fork(),fresh_maker()).first.cbinary(IMP) )
	if( auto const& imp2 = imp1->second.cbinary(IMP) )
	if( auto const& rel = gets_binary_sym(imp1->first) ) {
		auto const& ind = gets_rel_ind(*rel);
		if( !ind ) throw Error("\"unregistered relation\"")(*rel);
		_trans.emplace(*ind,thm);
		return *this;
	}
	throw Error("\"malformed trans\"")(thm);
}
Rewriter& Rewriter::register_cong( Thm const& thm ) & {
	// parsing congruence rule
	auto rule = Intro::rule(thm);
	Ctxt ctxt = rule.conclusion().ctxt();
	vector<Cong::Cond> conds;
	size_t rev = 0;
	while( ctxt.fixed(rev) ) rev++;
	while( auto o = ctxt.assumed(rev) ) {
		auto assm = *o;
		Term body = assm;
		bool abs;
		if( auto all = body.binder(ALL) ) {
			body = all->second;
			abs = true;
		} else {
			abs = false;
		}
		Opt<size_t> ind;
		while( auto x = strips_binary(body) ) {
			auto const* rel = &get<0>(*x);
			if( *rel == IMP ) {
				body = get<2>(*x);
				continue;
			}
			ind = gets_rel_ind(*rel);
			break;
		}
		if( !ind ) break;
		conds.emplace_back(*ind,abs,assm.capp()->second);
		rev++;
	}
	auto const& bin = strips_binary(rule.conclusion());
	if( !bin ) throw Error("\"malformed cong\"")(thm);
	auto const& [rel,l,r] = *bin;
	auto const& ind = gets_rel_ind(rel);
	if( !ind ) throw Error("\"unregistered relation\"")(rel);
	_congs[*ind].emplace_back(l,thm,std::move(conds));
	return *this;
}

Rewriter& Rewriter::register_dual( Thm const& thm ) & {
	Thm thm_strip = strip_all(thm,thm.ctxt().fork(),fresh_maker()).first;
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
			return *this;
		}
	}
	throw Error("\"malformed dual rule\"")(thm);
}

Opt<Thm> Rewriter::_step_abs( Rules const& rules, Thy const& thy, CTerm const& source, size_t ind, CTerm const& assm, Subst const& subst ) const {
	auto const& abs = source.bind();
	assert(abs);
	Thy subthy = thy.branch();
	CTerm v = subthy.fix(avoid(abs->first,[&](auto const& v){ return thy.has_constant(v); }));
	CTerm body = subthy.weaken(source).inst(v);
	Term prem = assm.Term::inst(subthy.cterm(abs->first)).subst(subst);
	while( auto imp = prem.binary(IMP) ) {
		add_forced(subthy,subthy.assume(imp->first));
		prem = imp->second;
	}
	if( auto const& eq = _step(rules,subthy,body,ind) ) {
		return eq->intro();
	}
	return {};
}

Opt<Thm> Rewriter::_step( Rules const& rules, Thy const& thy, CTerm const& source, size_t ind ) const {
	for( auto const& rule : rules[ind] ) {
		Ctxt const& pat_ctxt = rule.pat.ctxt();
		if( auto const& m = match( rule.pat, source, [&](auto v){ return pat_ctxt.fixes(v); }) ) {
			// source: l[m]
			Intp intp = Intp::make(pat_ctxt,rule.ctxt).compose(thy.interpret_ancestor(rule.ctxt));
			for(;;) {
				if( auto fix = intp.fixing() ) {
					// instantiate variables
					if( auto t = m->get(*fix) ) {
						intp.instantiate(*t);
					} else {
						intp.instantiate(thy.cterm(DUMMY));
					}
				} else if( auto assume = intp.assuming() ) {
					// discharge conditions
					intp.discharge(prove(*assume,thy));
				} else {
					break;
				}
			}
			return rule.rule.subst(intp); // l[m] = r[m]
		}
	}
	bool success = false;
	for( auto const& cong : _congs[ind] ) {
		Ctxt const& pat_ctxt = cong.pat.ctxt();
		if( auto const& m = match(cong.pat,source,[&](auto v){ return pat_ctxt.fixes(v); }) ) {// source: C[s...]
			Thm ret = thy.weaken(cong);
			// ret: ∀x... x'.... (φ ⟹ x = x') ⟹ ... ⟹ C[x...] = C[x'...]
			for( size_t i = 0; i<cong.conds.size(); i++ ) {
				auto v = pat_ctxt.fixed(i);
				assert(v);
				auto const& si = m->get(*v);
				if( !si ) throw Error("\"unexpected cong rule\"")(cong);
				auto cond = cong.conds[i];
				if( cond.abs ) {
					if( auto eq = _step_abs(rules,thy,*si,cond.ind,cond.assm,*m) ) {
						ret = match_discharge(ret,*eq);
						success = true;
					} else {
						return {};
					}
				} else if( auto eq = _step(rules,thy,*si,cond.ind) ) {
					ret = match_discharge(ret,*eq);
					success = true;
				} else {
					ret = ret << _make_refl(thy,*si,cond.ind);
				}
			}
			if( success ) {
				while( auto o = blasts(ret,thy) ) {// blasts remaining conditions
					ret = *o;
				}
				return ret;
			}
			return {};
		}
	}
	return {};
}

Opt<Thm> Rewriter::_step_abs( Rules const& rules, Thy const& thy, CTerm const& source, size_t ind, vector<char>::const_iterator pos_it, vector<char>::const_iterator pos_end ) const {
	auto const& abs = source.cbind();
	assert(abs);
	CTerm const& body = abs->second;
	if( auto const& eq = _step(rules,thy,body,ind,pos_it,pos_end) ) {
		return eq->intro();
	}
	return {};
}

Opt<Thm> Rewriter::_step( Rules const& rules, Thy const& thy, CTerm const& source, size_t ind, vector<char>::const_iterator pos_it, vector<char>::const_iterator pos_end ) const {
	if( pos_it == pos_end ) {// rewritable position
		return _step(rules,thy,source,ind);
	}
	for( auto const& cong : _congs[ind] ) {
		auto const& pat_ctxt = cong.pat.ctxt();// C[x...]
		if( auto const& m = match(cong.pat,source,[&](auto v){ return pat_ctxt.fixes(v); }) ) {// source: C[s...]
			Thm ret = thy.weaken(cong);// ret: ∀x. ∀y. x = y ⟹ ... ⟹ C[x...] = C[y...]
			size_t i = 0;
			auto var_end = cong.conds.size();
			assert( i != var_end );
			for(;;) {
				auto const& si = m->get(*pat_ctxt.fixed(i));
				assert(si);
				auto cond = cong.conds[i];
				if( *pos_it == i ) {// rewrite step must occur inside this position
					pos_it++;
					auto const& eq = cond.abs ? _step_abs(rules,thy,*si,cond.ind,pos_it,pos_end) : _step(rules,thy,*si,cond.ind,pos_it,pos_end);
					if( !eq ) return {};// no rewrite step was done
					ret = ret << *eq;// rewrite step was successful
					for(;;) {// remaining variables are instantiated as is
						i++;
						if( i == var_end ) break;
						ret = ret << _make_refl(thy,*m->get(*pat_ctxt.fixed(i)),cong.conds[i].ind);
					}
					while( auto o = blasts(ret,thy) ) {// blast conditions
						ret = *o;
					}
					return ret;
				}
				i++;
				if( i == var_end ) {
					return {};
				}
				ret = ret << _make_refl(thy,*si,cond.ind);
			}
		}
	}
	return {};
}

size_t Rewriter::_get_ind( Opt<std::string> const& rel ) const {
	if( rel ) {
		auto const& o = gets_rel_ind(*rel);
		if( !o ) throw Error("\"unregistered relation\"")(*rel);
		return *o;
	} else {
		return _default_ind;
	}
}

Opt<Thm> Rewriter::_steps(
	Rules const& rules,
	Thy const& thy,
	CTerm const& s,
	size_t min,
	size_t max,
	bool safe,
	vector<char> const& pos,
	size_t ind
) const {
	auto begin = pos.begin(), end = pos.end();
	auto const& init = _step(rules,thy,s,ind,begin,end);
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
	auto const& tranp = _trans.finds(ind);
	if( !tranp ) throw Error("\"transitivity rule unregistered\"");
	// ltrans: ∀y z. s = y ⟹ y = z ⟹ types... ⟹ s = z
	Thm ltrans = thy.weaken(tranp->second).instantiate(s);
	assert(eq.app());
	CTerm t = eq.capp()->second;
	for( unsigned int i = 1;; ) {
		auto const& step = _step(rules,thy,t,ind,begin,end);
		if( !step ) {
			if( i < min ) throw Error("\"too few steps\"")(to_string(i))(to_string(min))(t);
			return eq;
		}// t = u
		auto const& app = step->capp();
		assert(app);
		eq = ltrans << eq;// ∀z. t = z ⟹ types... ⟹ s = z
		eq = eq << *step;// types... ⟹ s = u
		while( auto imp = eq.cbinary(IMP) ) {// discharge types
			eq = eq.discharge(prove(imp->first,thy));
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
bool Rewriter::apply( Rules const& rules, Inference& thesis ) const {
	// thesis: s ⟹ rest
	auto const& goal = thesis.has_goal();
	if( !goal ) return false;
	auto const& o = _revimps.finds(_default_ind);// ∀x y. x = y ⟹ conds... ⟹ y ⟹ x
	auto const& thy = thesis.thy();
	auto steps = _steps(rules,thy,*goal,1,255,false,{},_default_ind);// s = t
	if( !steps ) return false;
	auto imp = thy.weaken(o->second.thm);// x = y ⟹ conds... ⟹ y ⟹ x
	imp = imp << *steps; // conditions... ⟹ t ⟹ s
	auto conds = o->second.conds;
	thesis.apply(Intro::imp(imp,conds+1));// conditions... ⟹ t ⟹ rest
	for( size_t i = 0; i < conds; i++ ) {
		thesis.blast();
	}// t ⟹ s
	return true;
}
bool Rewriter::apply( Rules const& rules, Inference& thesis, Ctrl const& ctrl ) const {
	// thesis: s ⟹ rest
	auto const& goal = thesis.has_goal();
	if( !goal ) return false;
	size_t ind = _get_ind(ctrl.rel);
	auto const& o = _revimps.finds(ind);// ∀x y. x = y ⟹ conds... ⟹ y ⟹ x
	if( !o ) throw Error("\"unregistered backward rewriting\"");
	auto const& thy = thesis.thy();
	auto steps = _steps(rules,thy,*goal,ctrl.min,ctrl.max,ctrl.safe,ctrl.pos,ind);// s = t
	if( !steps ) return false;
	auto imp = thy.weaken(o->second.thm);// x = y ⟹ conds... ⟹ y ⟹ x
	imp = imp << *steps; // conditions... ⟹ t ⟹ s
	auto conds = o->second.conds;
	thesis.apply(Intro::imp(imp,conds+1));// conditions... ⟹ t ⟹ rest
	for( size_t i = 0; i < conds; i++ ) {
		thesis.blast();
	}// t ⟹ s
	return true;
}
Thm Rewriter::rewrite( Rules const& rules, Thy const& thy, Thm const& source, Ctrl const& ctrl ) const {
	size_t ind = _get_ind(ctrl.rel);
	auto const& o = _imps.finds(ind);
	if( !o ) throw Error("\"unregistered forward rewriting\"");
	auto steps = _steps(rules,thy,source,ctrl.min,ctrl.max,ctrl.safe,ctrl.pos,ind);
	if( !steps ) {
		return source;
	}
	auto tmp = thy.weaken(o->second.thm);// (s ⟺ t) ⟹ conds... ⟹ s ⟹ t
	tmp = tmp << *steps;// conds... ⟹ s ⟹ t
	for( int i = 0; i < o->second.conds; i++ ) {
		tmp = blast(tmp,thy);
	}// s ⟹ t
	return tmp << source;
}
