#include <iostream>
#include "rewriter.hpp"

using namespace std;

static Error const MalformedRefl = Rewriter::Error("\"malformed reflexivity rule\"");
static Error const MalformedTrans = Rewriter::Error("\"malformed transitivity rule\"");
static Error const MalformedRule = Rewriter::Error("\"malformed rewrite rule\"");
static Error const MalformedCong = Rewriter::Error("\"malformed congruence rule\"");
Rewriter::Error const Rewriter::UnregisteredRel = Error("\"unregistered rewrite relation\"");
Rewriter::Error const Rewriter::MalformedImp = Error("\"malformed rewrite implication\"");
static Error const UnregisteredTrans = Rewriter::Error("\"missing setup trans\"");

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

void Rewriter::add_rule( Rules& rules, Thm const& thm, bool rev ) const {
	// checking well-formedness and extracting the lhs of the rewrite rule
	Ctxt loc = thm.ctxt().branch();
	Thm body = strip_all(thm,loc,fresh_maker());
	if( auto const& bin = strips_binary(body) )
	if( auto const& ind = gets_rel_ind(get<0>(*bin)) ) {
		if( rev ) {
			auto const& dual = _duals.finds(*ind);
			if( !dual ) throw Error("\"no dual rule registered\"");
			Thm dual_thm = dual->second.thm.weaken(loc) << body;
			rules[dual->second.ind].emplace_back(get<2>(*bin),dual_thm);
		} else {
			rules[*ind].emplace_back(get<1>(*bin),body);
		}
		return;
	}
	throw MalformedRule(thm);
}
void Rewriter::register_imp( Thm const& thm, bool dir ) {
	Thm rule = strip_all(thm);
	if( auto const& imp = rule.cbinary(IMP) )
	if( auto const& rel = gets_binary_sym(imp->first) ) {
		auto const& ind = gets_rel_ind(*rel);
		if( !ind ) throw UnregisteredRel(*rel);
		( dir ? _imps : _revimps ).emplace(*ind,thm);
		return;
	}
	throw MalformedImp(thm);
}
void Rewriter::register_refl( Thm const& thm ) {
	Thm rule = strip_all(thm);
	auto const& rel = gets_binary_sym(rule);
	if( !rel ) throw MalformedRefl(thm);
	size_t ind = _rels.size();
	_rels.emplace(*rel,ind);
	_refls.emplace_back(thm);
	_congs.emplace_back();
}
void Rewriter::register_trans( Thm const& thm ) {
	if( auto const& imp1 = strip_all(thm).cbinary(IMP) )
	if( auto const& imp2 = imp1->second.cbinary(IMP) )
	if( auto const& rel = gets_binary_sym(imp2->second) ) {
		auto const& ind = gets_rel_ind(*rel);
		if( !ind ) throw UnregisteredRel(*rel);
		_trans.emplace(*ind,thm);
		return;
	}
	throw MalformedTrans(thm);
}
void Rewriter::register_cong( Thm const& thm ) {
	// parsing congruence rule
	auto rule = Inference::rule(thm);
	Ctxt ctxt = rule.ctxt();
	size_t rev = 0;
	vector<size_t> inds;
	vector<bool> abss;
	while( ctxt.fixed(rev) ) rev++;
	while( auto const& o = ctxt.assumed(rev) ) {
		Term assm = *o;
		if( auto const& all = assm.binder(ALL) ) {
			assm = all->second;
			abss.emplace_back(true);
		} else {
			abss.emplace_back(false);
		}
		auto const& rel = gets_binary_sym(assm);
		if( !rel ) {
			throw MalformedCong(thm);
		}
		auto const& ind = gets_rel_ind(*rel);
		if( !ind ) {
			throw UnregisteredRel(*rel)("#in_congruence")(thm);
		}
		inds.emplace_back(*ind);
		rev++;
	}
	auto const& bin = strips_binary(rule.conclusion());
	if( !bin ) throw MalformedCong(thm);
	auto const& [rel,l,r] = *bin;
	auto const& ind = gets_rel_ind(rel);
	if( !ind ) throw UnregisteredRel(rel);
	auto const& pat = thm.ctxt().branch().enclose(l);
	_congs[*ind].emplace_back(pat,thm,std::move(inds),std::move(abss));
}

void Rewriter::register_dual( Thm const& thm ) {
	Ctxt loc = thm.ctxt().branch();
	Thm thm_strip = strip_all(thm,loc);
	if( auto const& imp = thm_strip.cbinary(IMP) )
	if( auto const& bin1 = strips_binary(imp->first) )
	if( auto const& ind1 = gets_rel_ind(get<0>(*bin1)) )
	if( auto const& bin2 = strips_binary(imp->second) )
	if( auto const& ind2 = gets_rel_ind(get<0>(*bin2)) ) {
		_duals.emplace(*ind2,Dual(thm,*ind1));
		return;
	}
	throw Error("\"malformed dual rule\"")(thm);
}

Opt<Thm> Rewriter::_step_abs( Rules const& rules, CTerm const& source, size_t ind ) const {
	auto const& abs = source.cabs();
	assert(abs);
	CTerm const& body = abs->second;
	if( auto const& eq = _step(rules,body,ind) ) {
		return eq->intro();
	}
	return {};
}

Opt<Thm> Rewriter::_step( Rules const& rules, CTerm const& source, size_t ind ) const {
	auto const& source_ctxt = source.ctxt();
	for( auto const& rule : rules[ind] ) {
		Ctxt const& rule_ctxt = rule.pat.ctxt();
		if( auto const& m = match( rule.pat, source, [&](auto v){ return rule_ctxt.fixes(v); }) ) {
			// source: l[m]
			auto intp = Intp(rule_ctxt,source_ctxt);
			for( int i = 0; i < rule_ctxt.revision(); i++ ) {
				auto v = rule_ctxt.fixed(i);
				assert(v);
				intp.instantiate(*m->get(*v));
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
DEB(source << "  cong " << ret);
			// ret: ∀x. ∀x'. x = x' ⟹ ... ⟹ C[x...] = C[x'...]
			size_t n = pat_ctxt.revision();
			for( size_t i = 0; i < n; i++ ) {
				auto v = pat_ctxt.fixed(i);
				assert(v);
DEB( *v << " := " << *m->get(*v) );
				auto const& si = m->get(*v);
				assert(si);
				size_t ind_i = cong.inds[i];
				if( cong.abss[i] ) {
					if( auto const& eq = _step_abs(rules,*si,ind_i) ) {
						ret = *match_discharge(ret,*eq);
						success = true;
					} else {
						return {};
					}
				} else if( auto const& eq = _step(rules,*si,ind_i) ) {
					ret = *match_discharge(ret,*eq);
					success = true;
				} else {
					ret = ret << _refls[ind_i].weaken(source_ctxt).allE(*si);
				}
DEB(ret);
			}
			if( success ) return ret;
			return {};
		}
	}
	return {};
}

Opt<Thm> Rewriter::_step_abs( Rules const& rules, CTerm const& source, size_t ind, vector<char>::const_iterator pos_it, vector<char>::const_iterator pos_end ) const {
	auto const& abs = source.cabs();
	assert(abs);
	CTerm const& body = abs->second;
	if( auto const& eq = _step(rules,body,ind,pos_it,pos_end) ) {
		return eq->intro();
	}
	return {};
}

Opt<Thm> Rewriter::_step( Rules const& rules, CTerm const& source, size_t ind, vector<char>::const_iterator pos_it, vector<char>::const_iterator pos_end ) const {
	if( pos_it == pos_end ) {// rewritable position
		return _step(rules,source,ind);
	}
	auto const& source_ctxt = source.ctxt();
	for( auto const& cong : _congs[ind] ) {
		auto const& pat_ctxt = cong.pat.ctxt();// C[x...]
		if( auto const& m = match(cong.pat,source,[&](auto v){ return pat_ctxt.fixes(v); }) ) {// source: C[s...]
			Thm ret = cong.weaken(source_ctxt);// ret: ∀x. ∀y. x = y ⟹ ... ⟹ C[x...] = C[y...]
			size_t i = 0;
			auto var_end = pat_ctxt.revision();
			assert( i != var_end );
			for(;;) {
				auto const& si = m->get(*pat_ctxt.fixed(i));
				assert(si);
				auto const& ind_i = cong.inds[i];
				if( *pos_it == i ) {// rewrite step must occur inside this position
					pos_it++;
					auto const& eq = cong.abss[i] ? _step_abs(rules,*si,ind_i,pos_it,pos_end) : _step(rules,*si,ind_i,pos_it,pos_end);
					if( !eq ) return {};// no rewrite step was done
					ret = ret << *eq;// rewrite step was successful
					for(;;) {// remaining variables are instantiated as is
						i++;
						if( i == var_end ) return ret;
						ret = ret << _refls[cong.inds[i]].weaken(source_ctxt).allE(*m->get(*pat_ctxt.fixed(i)));
					}
				}
				i++;
				if( i == var_end ) {
					return {};
				}
				ret = ret << _refls[ind_i].weaken(source_ctxt).allE(*si);
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

Thm Rewriter::_steps(
	Rules const& rules,
	CTerm const& source,
	unsigned int min, unsigned int max, bool safe,
	vector<char> const& pos,
	size_t ind
) const {
	Ctxt const& source_ctxt = source.ctxt();
	Thm lrefl = _refls[ind].weaken(source_ctxt);// ∀P. P ⟺ P
	Thm eq = lrefl.allE(source);// source ⟺ source
	auto const& tranp = _trans.finds(ind);
	if( !tranp ) throw UnregisteredTrans;
	Thm ltrans = tranp->second.weaken(source_ctxt).allE(source);// ∀Q R. (source ⟺ Q) ⟹ (Q ⟺ R) ⟹ (source ⟺ R)
	auto begin = pos.begin(), end = pos.end();
	CTerm s = source;
	for( unsigned int i = 0;; i++ ) {
		if( i == max ) {
			if( safe ) break;
			throw Error("\"rewrite limit exceeded\"")(to_string(max));
		}
		auto const& step = _step(rules,s,ind,begin,end);
		if( !step ) {
			if( i < min ) {
				throw TooFewSteps(i,min,source);
			} else {
				return eq;
			}
		}
		auto const& app = step->capp();
		assert(app);
		CTerm const& t = app->second;
		Thm tr = ltrans.allE(s).allE(t).impE(eq);
		eq = tr.impE(*step);
		s = t;
	}
	return eq;// source ⟺ target
}
void Rewriter::apply( Rules const& rules, Inference& thesis, unsigned int min, unsigned int max, bool safe, std::vector<char> const& pos, Opt<std::string> const& rel ) const {
	// thesis: s ⟹ ...
	auto const& goal = thesis.has_goal();
	if( !goal ) throw Error("\"no goal to rewrite\"");
	size_t ind = _get_ind(rel);
	auto const& o = _revimps.finds(ind);// ∀x y. x = y ⟹ y ⟹ x
	if( !o ) throw Error("\"unregistered backward rewriting\"");
	auto eq = _steps(rules,*goal,min,max,safe,pos,ind);// s = t
	auto imp = o->second.weaken(thesis.locale()) << eq;// t ⟹ s
	thesis.apply(Inference::rule(imp));// t ⟹ ...
}
Thm Rewriter::rewrite( Rules const& rules, Thm const& source, unsigned int min, unsigned int max, bool safe, vector<char> const& pos, Opt<std::string> const& rel ) const {
	size_t ind = _get_ind(rel);
	auto const& o = _imps.finds(ind);
	if( !o ) throw Error("\"unregistered forward rewriting\"");
	auto eq = _steps(rules,source,min,max,safe,pos,ind);
	return o->second.weaken(source.ctxt()) << eq << source;
}
