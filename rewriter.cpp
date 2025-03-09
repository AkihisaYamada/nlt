#include <iostream>
#include "rewriter.hpp"

using namespace std;

string const Rewriter::CONG = "#cong";

static Error const MalformedRefl = Rewriter::Error("\"malformed reflexivity rule\"");
static Error const MalformedTrans = Rewriter::Error("\"malformed transitivity rule\"");
static Error const MalformedRule = Rewriter::Error("\"malformed rewrite rule\"");
static Error const MalformedCong = Rewriter::Error("\"malformed congruence rule\"");
Rewriter::Error const Rewriter::UnregisteredRel = Error("\"unregistered rewrite relation\"");
Rewriter::Error const Rewriter::MalformedImp = Error("\"malformed rewrite implication\"");
static Error const UnregisteredTrans = Rewriter::Error("\"missing setup trans\"");

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

void Rewriter::add_rule( Locale const& loc, Rules& rules, Thm const& thm, bool rev ) const {
	// checking well-formedness and extracting the lhs of the rewrite rule
	Locale subloc = loc.branch();
	Thm body = strip_all(thm,subloc,fresh_maker()).first;
	while( auto imp = body.cbinary(IMP) ) {
		Thm assm = subloc.assume(imp->first);
		add_forced(subloc,assm);
		body = body.discharge(assm);
	}
	if( auto const& bin = strips_binary(body) )
	if( auto const& ind = gets_rel_ind(get<0>(*bin)) ) {
		if( rev ) {
			auto const& dual = _duals.finds(*ind);
			if( !dual ) throw Error("\"no dual rule registered\"");
			Thm dual_thm = dual->second.thm.weaken(subloc) << body;
			while( auto o = blasts(dual_thm,subloc) ) {
				dual_thm = *o;
			}
			rules[dual->second.ind].emplace_back(get<2>(*bin),dual_thm);
		} else {
			rules[*ind].emplace_back(get<1>(*bin),body);
		}
		return;
	}
	throw MalformedRule(thm);
}
void Rewriter::register_imp( Thm const& thm, bool dir ) {
	Thm rule = strip_all(thm).first;// x = y ⟹ x ⟹ conds... ⟹ y
	if( auto const& imp = rule.cbinary(IMP) )// x ⟹ conds... ⟹ y
	if( auto const& imp2 = imp->second.cbinary(IMP) )// conds ... ⟹ y
	if( auto const& rel = gets_binary_sym(imp->first) ) {
		auto const& ind = gets_rel_ind(*rel);
		if( !ind ) throw UnregisteredRel(*rel);
		Term t = imp2->second;
		size_t conds = 0;
		while( auto imp3 = t.binary(IMP) ) {
			t = imp3->second;
			conds++;
		}
		( dir ? _imps : _revimps ).emplace(*ind,Imp{thm,conds});
		return;
	}
	throw MalformedImp(thm);
}
void Rewriter::register_refl( Thm const& thm ) {
	auto rule = Intro::rule(thm);
	auto const& rel = gets_binary_sym(rule.conclusion());
	if( !rel ) throw MalformedRefl(thm);
	size_t ind = _rels.size();
	_rels.emplace(*rel,ind);
	_refls.emplace_back(thm);
	_congs.emplace_back();
}
void Rewriter::register_trans( Thm const& thm ) {
	if( auto const& imp1 = strip_all(thm).first.cbinary(IMP) )
	if( auto const& imp2 = imp1->second.cbinary(IMP) )
	if( auto const& rel = gets_binary_sym(imp1->first) ) {
		auto const& ind = gets_rel_ind(*rel);
		if( !ind ) throw UnregisteredRel(*rel);
		_trans.emplace(*ind,thm);
		return;
	}
	throw MalformedTrans(thm);
}
void Rewriter::register_cong( Thm const& thm ) {
	// parsing congruence rule
	auto rule = Intro::rule(thm);
	Ctxt ctxt = rule.ctxt();
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
	if( !bin ) throw MalformedCong(thm);
	auto const& [rel,l,r] = *bin;
	auto const& ind = gets_rel_ind(rel);
	if( !ind ) throw UnregisteredRel(rel);
	_congs[*ind].emplace_back(l,thm,std::move(conds));
}

void Rewriter::register_dual( Thm const& thm ) {
	Ctxt loc = thm.ctxt().branch();
	Thm thm_strip = strip_all(thm,loc).first;
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

Opt<Thm> Rewriter::_step_abs( Rules const& rules, Locale const& loc, CTerm const& source, size_t ind, CTerm const& assm, CSubst const& subst ) const {
	auto const& abs = source.cabs();
	assert(abs);
	CTerm body = abs->second;
	auto subloc = Locale(loc,body.ctxt());
	Term prem = assm.Term::inst(subloc.cterm(abs->first)).subst(subst);
	while( auto imp = prem.binary(IMP) ) {
		add_forced(subloc,subloc.assume(imp->first));
		prem = imp->second;
	}
	if( auto const& eq = _step(rules,subloc,body,ind) ) {
		return eq->intro();
	}
	return {};
}

Opt<Thm> Rewriter::_step( Rules const& rules, Locale const& loc, CTerm const& source, size_t ind ) const {
	auto const& source_ctxt = source.ctxt();
	for( auto const& rule : rules[ind] ) {
		Ctxt const& rule_ctxt = rule.pat.ctxt();
		if( auto const& m = match( rule.pat, source, [&](auto v){ return rule_ctxt.fixes(v); }) ) {
			// source: l[m]
			auto intp = Intp(rule_ctxt,source_ctxt);
			// instantiate variables
			while( auto v = intp.fixing() ) {
				intp.instantiate(*m->get(*v));
			}
			// discharge conditions
			while( auto assm = intp.assuming() ) {
				intp.discharge(prove(*assm,loc));
			}
			auto const& ret = intp.subst(rule.thm); // l[m] = r[m]
			return ret;
		}
	}
	bool success = false;
	for( auto const& cong : _congs[ind] ) {
		Ctxt const& pat_ctxt = cong.pat.ctxt();
		if( auto const& m = match(cong.pat,source,[&](auto v){ return pat_ctxt.fixes(v); }) ) {// source: C[s...]
			Thm ret = cong.weaken(source_ctxt);
			// ret: ∀x... x'.... (φ ⟹ x = x') ⟹ ... ⟹ C[x...] = C[x'...]
			for( size_t i = 0; i<cong.conds.size(); i++ ) {
				auto v = pat_ctxt.fixed(i);
				assert(v);
				auto const& si = m->get(*v);
				if( !si ) throw Error("\"unexpected cong rule\"")(cong);
				auto cond = cong.conds[i];
				if( cond.abs ) {
					if( auto eq = _step_abs(rules,loc,*si,cond.ind,cond.assm,*m) ) {
						auto o = match_discharge(ret,*eq);
						assert(o);
						ret = *o;
						success = true;
					} else {
						return {};
					}
				} else if( auto eq = _step(rules,loc,*si,cond.ind) ) {
					auto o = match_discharge(ret,*eq);
					assert(o);
					ret = *o;
					success = true;
				} else {
					Thm refl = _refls[cond.ind].weaken(source_ctxt).instantiate(*si);
					while( auto imp = refl.cbinary(IMP) ) {
						refl = refl.discharge(prove(imp->first,loc));
					}
					ret = ret << refl;
				}
			}
			if( success ) {
				while( auto o = blasts(ret,loc) ) {// blasts remaining conditions
					ret = *o;
				}
				return ret;
			}
			return {};
		}
	}
	return {};
}

Opt<Thm> Rewriter::_step_abs( Rules const& rules, Locale const& loc, CTerm const& source, size_t ind, vector<char>::const_iterator pos_it, vector<char>::const_iterator pos_end ) const {
	auto const& abs = source.cabs();
	assert(abs);
	CTerm const& body = abs->second;
	if( auto const& eq = _step(rules,loc,body,ind,pos_it,pos_end) ) {
		return eq->intro();
	}
	return {};
}

Opt<Thm> Rewriter::_step( Rules const& rules, Locale const& loc, CTerm const& source, size_t ind, vector<char>::const_iterator pos_it, vector<char>::const_iterator pos_end ) const {
	if( pos_it == pos_end ) {// rewritable position
		return _step(rules,loc,source,ind);
	}
	auto const& source_ctxt = source.ctxt();
	for( auto const& cong : _congs[ind] ) {
		auto const& pat_ctxt = cong.pat.ctxt();// C[x...]
		if( auto const& m = match(cong.pat,source,[&](auto v){ return pat_ctxt.fixes(v); }) ) {// source: C[s...]
			Thm ret = cong.weaken(source_ctxt);// ret: ∀x. ∀y. x = y ⟹ ... ⟹ C[x...] = C[y...]
			size_t i = 0;
			auto var_end = cong.conds.size();
			assert( i != var_end );
			for(;;) {
				auto const& si = m->get(*pat_ctxt.fixed(i));
				assert(si);
				auto cond = cong.conds[i];
				if( *pos_it == i ) {// rewrite step must occur inside this position
					pos_it++;
					auto const& eq = cond.abs ? _step_abs(rules,loc,*si,cond.ind,pos_it,pos_end) : _step(rules,loc,*si,cond.ind,pos_it,pos_end);
					if( !eq ) return {};// no rewrite step was done
					ret = ret << *eq;// rewrite step was successful
					for(;;) {// remaining variables are instantiated as is
						i++;
						if( i == var_end ) break;
						Thm refl = _refls[cong.conds[i].ind].weaken(source_ctxt).instantiate(*m->get(*pat_ctxt.fixed(i)));
						while( auto o = blasts(refl,loc) ) {
							refl = *o;
						}
						ret = ret << refl;
					}
					while( auto o = blasts(ret,loc) ) {// blast conditions
						ret = *o;
					}
					return ret;
				}
				i++;
				if( i == var_end ) {
					return {};
				}
				auto ref = _refls[cond.ind].weaken(source_ctxt).instantiate(*si);
				while( auto o = blasts(ref,loc) ) {
					ref = *o;
				}
				ret = ret << ref;
			}
		}
	}
	return {};
}

size_t Rewriter::_get_ind( Opt<std::string> const& rel ) const {
	if( rel ) {
		auto const& o = gets_rel_ind(*rel);
		if( !o ) throw UnregisteredRel(*rel);
		return *o;
	} else {
		return 0;
	}
}

Opt<Thm> Rewriter::_steps(
	Rules const& rules,
	Locale const& loc,
	CTerm const& s,
	size_t min,
	size_t max,
	bool safe,
	vector<char> const& pos,
	size_t ind
) const {
	auto begin = pos.begin(), end = pos.end();
	auto const& init = _step(rules,loc,s,ind,begin,end);
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
	if( !tranp ) throw UnregisteredTrans;
	// ltrans: ∀y z. s = y ⟹ y = z ⟹ types... ⟹ s = z
	Thm ltrans = tranp->second.weaken(s.ctxt()).instantiate(s);
	assert(eq.app());
	CTerm t = eq.capp()->second;
	for( unsigned int i = 1;; ) {
		auto const& step = _step(rules,loc,t,ind,begin,end);
		if( !step ) {
			if( i < min ) throw TooFewSteps(i,min,t);
			return eq;
		}// t = u
		i++;
		if( i == max ) {
			if( !safe )
				throw Error("\"rewrite limit exceeded\"")(to_string(max));
			return eq;
		}
		auto const& app = step->capp();
		assert(app);
		eq = ltrans << eq;// ∀z. t = z ⟹ types... ⟹ s = z
		eq = eq << *step;// types... ⟹ s = u
		while( auto imp = eq.cbinary(IMP) ) {// discharge types
			eq = eq.discharge(prove(imp->first,loc));
		}
		t = app->second;
	}
}
bool Rewriter::apply( Rules const& rules, Inference& thesis, Ctrl const& ctrl ) const {
	// thesis: s ⟹ rest
	auto const& goal = thesis.has_goal();
	if( !goal ) return false;
	size_t ind = _get_ind(ctrl.rel);
	auto const& o = _revimps.finds(ind);// ∀x y. x = y ⟹ conditions ⟹ y ⟹ x
	if( !o ) throw Error("\"unregistered backward rewriting\"");
	auto const& loc = thesis.locale();
	auto steps = _steps(rules,loc,*goal,ctrl.min,ctrl.max,ctrl.safe,ctrl.pos,ind);// s = t
	if( !steps ) return false;
	auto imp = o->second.thm.weaken(loc);// x = y ⟹ conditions... ⟹ y ⟹ x
	imp = imp << *steps; // conditions... ⟹ t ⟹ s
	for( size_t i = 0; i < o->second.conds; i++ ) {
		imp = blast(imp,loc);
	}// t ⟹ s
	thesis.apply(Intro::imp(imp));// t ⟹ rest
	return true;
}
Thm Rewriter::rewrite( Rules const& rules, Locale const& loc, Thm const& source, Ctrl const& ctrl ) const {
	size_t ind = _get_ind(ctrl.rel);
	auto const& o = _imps.finds(ind);
	if( !o ) throw Error("\"unregistered forward rewriting\"");
	auto steps = _steps(rules,loc,source,ctrl.min,ctrl.max,ctrl.safe,ctrl.pos,ind);
	if( !steps ) {
		return source;
	}
	auto tmp = o->second.thm.weaken(loc);
	tmp = tmp << *steps;
	for( int i = 0; i < o->second.conds; i++ ) {
		tmp = *blasts(tmp,loc);
	}// s ⟹ t
	return tmp << source;
}
