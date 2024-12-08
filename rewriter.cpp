#include <iostream>
#include "rewriter.hpp"

using namespace std;

static Error const MalformedRefl = Rewriter::Error("\"malformed reflexivity rule\"");
static Error const MalformedCong = Rewriter::Error("\"malformed congruence rule\"");
static Error const UnregisteredRel = Rewriter::Error("\"unregistered rewrite relation\"");

Opt<tuple<string,CTerm,CTerm>> strips_binary( CTerm const& term ) {
	if( auto const& app = term.capp() )
	if( auto const& app2 = app->first.capp() )
	if( auto const& rel = app2->first.sym() ) {
		return {{*rel,app2->second,app->second}};
	}
	return {};
}

void Rewriter::add_rule( Rules& rules, Thm const& thm, bool rev ) const {
	// checking well-formedness and extracting the lhs of the rewrite rule
	Ctxt loc = thm.ctxt().branch();
	Thm body = strip_all(thm,loc,fresh_maker());
	if( auto const& bin = strips_binary(body) )
	if( auto const& ind = gets_rel_ind(get<0>(*bin)) ) {
		if( rev ) {
			auto const& dual = _duals.finds(ind);
			if( !dual ) throw Error("\"no dual rule registered\"");
			Thm body2 = dual->second.thm.weaken(loc) << body;
			rules[dual->second.ind].emplace_back(body2.intro(),body2);
		} else {
			rules[*ind].emplace_back(get<1>(*bin),body);
		}
		return;
	}
	throw Error(thm);
}
void Rewriter::register_refl( Thm const& thm ) {
	Ctxt ctxt = thm.ctxt().branch();
	Thm rule = strip_all(thm,ctxt);
	auto const& bin = strips_binary(rule);
	if( !bin ) throw MalformedRefl(thm);
	size_t ind = _rels.size();
	_rels.emplace(get<0>(*bin),ind);
	_refls.emplace_back(thm);
	_congs.emplace_back();
}
void Rewriter::register_cong( Thm const& thm ) {
	// parsing congruence rule
	Thm rule = make_rule(thm);
	Ctxt ctxt = rule.ctxt();
	size_t rev = 0;
	vector<size_t> inds;
	while( ctxt.fixed(rev) ) rev++;
	while( auto const& assm = ctxt.assumed(rev) ) {
		if( auto const& bin = strips_binary(*assm) )
		if( auto const& ind = gets_rel_ind(get<0>(*bin)) ) {
			inds.emplace_back(*ind);
			rev++;
			continue;
		}
		throw MalformedCong(thm);
	}
	auto const& bin = strips_binary(rule);
	if( !bin ) throw MalformedCong(thm);
	auto const& [rel,l,r] = *bin;
	auto const& ind = gets_rel_ind(rel);
	if( !ind ) throw UnregisteredRel(rel);
	auto const& pat = thm.ctxt().branch().enclose(l);
	_congs[*ind].emplace_back(pat,thm,std::move(inds));
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
	if( auto const& abs = source.cabs() ) {
		CTerm const& body = abs->second;
		if( auto const& eq = _step(rules,body,ind) ) {
			return eq->intro();
		}
	} else {
		return _step(rules,source,ind);
	}
	return {};
}

Opt<Thm> Rewriter::_step( Rules const& rules, CTerm const& source, size_t ind ) const {
	auto const& source_ctxt = source.ctxt();
	for( auto const& rule : rules[ind] ) {
		Ctxt const& rule_ctxt = rule.pat.ctxt();
		if( auto const& m = match(rule_ctxt.fvars(),rule.pat,source) ) {
			// source: l[m]
			Intp intp = Intp::make(rule_ctxt,source_ctxt);
			for( int i = 0; i < rule_ctxt.revision(); i++ ) {
				auto v = rule_ctxt.fixed(i);
				assert(v);
				intp.instantiate(*m->get(*v));
			}
			return intp.subst(rule.thm); // l[m] = r[m]
		}
	}
	bool success = false;
	for( auto const& cong : _congs[ind] ) {
		Ctxt const& ctxt = cong.pat.ctxt();
		if( auto const& m = match(ctxt.fvars(),cong.pat,source) ) {// source: C[s...]
			Thm ret = cong.thm.weaken(source_ctxt);
			// ret: ∀x. ∀x'. x = x' ⟹ ... ⟹ C[x...] = C[x'...]
			size_t n = ctxt.revision();
			for( size_t i = 0; i < n; i++ ) {
				auto v = ctxt.fixed(i);
				assert(v);
				auto const& si = m->get(*v);
				assert(si);
				size_t ind_i = cong.inds[i];
				if( auto const& eq = _step_abs(rules,*si,ind_i) ) {
					ret = ret << *eq;
					success = true;
				} else {
					ret = ret << _refls[ind_i].weaken(source_ctxt).allE(*si);
				}
			}
			if( success ) return ret;
			return {};
		}
	}
	return {};
}

Opt<Thm> Rewriter::_step_abs( Rules const& rules, CTerm const& source, size_t ind, vector<char>::const_iterator pos_it, vector<char>::const_iterator pos_end ) const {
	if( auto const& abs = source.cabs() ) {
		CTerm const& body = abs->second;
		if( auto const& eq = _step(rules,body,ind,pos_it,pos_end) ) {
			return eq->intro();
		}
	} else {
		return _step(rules,source,ind,pos_it,pos_end);
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
		auto const& inds = cong.inds;// relation indices
		if( auto const& m = match(pat_ctxt.fvars(),cong.pat,source) ) {// source: C[s...]
			Thm ret = cong.thm.weaken(source_ctxt);// ret: ∀x. ∀y. x = y ⟹ ... ⟹ C[x...] = C[y...]
			size_t i = 0;
			auto var_end = pat_ctxt.revision();
			assert( i != var_end );
			for(;;) {
				auto const& si = m->get(*pat_ctxt.fixed(i));
				assert(si);
				auto const& ind_i = cong.inds[i];
				if( *pos_it == i ) {// rewrite step must occur inside this position
					pos_it++;
					auto const& eq = _step_abs(rules,*si,ind_i,pos_it,pos_end);
					if( !eq ) return {};// no rewrite step was done
					ret = discharge(ret,*eq);// rewrite step was successful
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
				ret = discharge(ret,_refls[ind_i].allE(*si));
			}
		}
	}
	return {};
}

Thm Rewriter::steps(Rules const& rules, CTerm const& source, unsigned int min, unsigned int max, bool safe, vector<char> const& pos) const {
	Ctxt const& source_ctxt = source.ctxt();
	Thm lrefl = _refls[0].weaken(source_ctxt);// ∀P. P ⟺ P
	Thm eq = lrefl.allE(source);// source ⟺ source
	Thm ltrans = _trans[0].weaken(source_ctxt).allE(source);// ∀Q R. (source ⟺ Q) ⟹ (Q ⟺ R) ⟹ (source ⟺ R)
	auto begin = pos.begin(), end = pos.end();
	CTerm s = source;
	for( unsigned int i = 0;; i++ ) {
		if( i == max ) {
			if( safe ) break;
			throw Error("\"rewrite limit exceeded\"")(to_string(max));
		}
		auto const& step = _step(rules,s,0,begin,end);
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
Thm Rewriter::rewrite(Rules const& rules, Thm const& source, unsigned int min, unsigned int max, bool safe, vector<char> const& pos) const {
	Thm const& eq = steps(rules,source,min,max,safe,pos);
	auto const& app = eq.capp();
	assert(app);
	CTerm const& target = app->second;
	return imp.weaken(source.ctxt()).allE(source).allE(target).impE(eq).impE(source);
}
