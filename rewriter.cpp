#include <iostream>
#include "util.hpp"

using namespace std;

Rewriter::Rules& Rewriter::Rules::add(Thm const& thm) {
	// checking well-formedness and extracting the lhs of the rewrite rule
	Ctxt loc = thm.ctxt().branch();
	Thm body = strip_all(thm,loc);
	auto const& app = body.app();
	if( !app ) {
		throw Error(thm);
	}
	auto const& app2 = app->first.app();
	if( !app2 ) {
		throw Error(thm);
	}
	push_back({app2->second,thm});
	return *this;
}

static Thm equate_cong(Thm const& cong, Thm const& eq, CTerm const& arg) {
	return discharge(cong.weaken(eq.ctxt()),eq) // ∀x. s x = t x
			.allE(arg);// s arg = t arg
}

static Thm equate_abs(Thm const& ext, Thm const& eq) {
	Thm all = eq.intro();// ∀x. s = t
	auto const& app = eq.app();
	assert(app);
	auto const& app2 = app->first.app();
	assert(app2);
	CTerm const& s = app2->second.lift();// x. s
	CTerm const& t = app->second.lift();// x. t
	return ext.weaken(all.ctxt()).allE(s).allE(t).impE(all);// (x. s) = (x. t)
}


static Thm equate_quantified(Thm const& ext, Thm const& eq) {
	Thm all = eq.intro();// ∀x. s = t
	auto const& app = eq.app();
	assert(app);
	auto const& app2 = app->first.app();
	assert(app2);
	CTerm const& s = app2->second.lift();// x. s
	CTerm const& t = app->second.lift();// x. t
	return ext.weaken(all.ctxt()).allE(s).allE(t).impE(all);// (ξ x. s) = (ξ x. t)
}

Opt<Thm> Rewriter::_step(Rules const& rules, CTerm const& source, Thm const& refl) const {
	for( auto const& rule : rules ) {
		Ctxt const& ctxt = rule.pat.ctxt();
		if( auto const& m = match(ctxt.fvars(),rule.pat,source) ) {
			// source = lθ
			Thm ret = rule.thm.weaken(source.ctxt());// ret = ∀x... l = r
			for( auto const& var : ctxt.fvar_list() ) {
				ret = ret.allE(*m->get(var));
			}
			return ret; // lθ = rθ
		}
	}
	for( auto const& cong : congs ) {
		Ctxt const& ctxt = cong.pat.ctxt();
		if( auto const& m = match(ctxt.fvars(),cong.pat,source) ) {// source = C[s...]
			Thm ret = cong.thm.weaken(source.ctxt());// ret = ∀x. ∀x'. x = x' ⟹ ... ⟹ C[x...] = C[x'...]
			auto it = ctxt.fvar_list().begin();
			auto end = ctxt.fvar_list().end();
			for(;;) {
				auto const& si = m->get(*it);
				assert(si);
				it++;
				if( auto const& eq = _step(rules,*si,refl) ) {
					ret = discharge(ret,*eq);
					break;
				}
				if( it == end ) {
					return {};
				}
				ret = discharge(ret,refl.allE(*si));
			}
			for( ; it != end; it++ ) {
				ret = discharge(ret,refl.allE(*m->get(*it)));
			}
			return ret;
		}
	}
	for( auto const& qcong : quantifier_congs ) {
		Ctxt const& ctxt = qcong.pat.ctxt();
		if( auto const& m = match(ctxt.fvars(),qcong.pat,source) ) {// source = (ξ) α
			for( auto const& var : ctxt.fvar_list() ) {// shouldn't loop more than once
				auto const& s = m->get(var);
				assert(s);
				auto const& abs = s->abs();
				if( abs ) {
					CTerm const& s = abs->second;
					auto const& eq = _step(rules,s,refl.weaken(s.ctxt()));
					if( eq ) {
						return equate_abs(qcong.thm,*eq);
					}
				}
			}
			return {};
		}
	}
	return {};
}

Opt<Thm> Rewriter::_step(Rules const& rules, CTerm const& source, vector<char>::const_iterator pos_it, vector<char>::const_iterator pos_end, Thm const& refl) const {
	if( pos_it == pos_end ) {// rewritable position
		return _step(rules,source,refl);
	}
	for( auto const& cong : congs ) {
		auto const& ctxt = cong.pat.ctxt();
		if( auto const& m = match(ctxt.fvars(),cong.pat,source) ) {// source = C[s...]
			Thm ret = cong.thm.weaken(source.ctxt());// ret = ∀x. ∀x'. x = x' ⟹ ... ⟹ C[x...] = C[x'...]
			auto var_it = ctxt.fvar_list().begin();
			auto var_end = ctxt.fvar_list().end();
			assert( var_it != var_end );
			char i = 0;
			for(;;) {
				auto const& si = m->get(*var_it);
				assert(si);
				var_it++;
				if( *pos_it == i ) {// rewrite step must occur inside this position
					pos_it++;
					if( auto const& eq = _step(rules,*si,pos_it,pos_end,refl) ) {
						// rewrite step was successful
						ret = discharge(ret,*eq);
						break;
					}
					return {};// no rewrite step was done
				} else if( var_it == var_end ) {
					return {};
				} else {
					ret = discharge(ret,refl.allE(*si));
					i++;
				}
			}
			for( ; var_it != var_end; var_it++ ) {// remaining variables are instantiated as is
				ret = discharge(ret,refl.allE(*m->get(*var_it)));
			}
			return ret;
		}
	}
	for( auto const& qcong : quantifier_congs ) {
		Ctxt const& ctxt = qcong.pat.ctxt();
		auto const& m = match(ctxt.fvars(),qcong.pat,source);
		if( m ) {// source = (ξ) α
			for( auto const& var : ctxt.fvar_list() ) {// shouldn't loop more than once
				auto const& s = m->get(var);
				assert(s);
				auto const& abs = s->abs();
				if( abs ) {
					pos_it++;
					auto const& eq = _step(rules,abs->second,pos_it,pos_end,refl);
					if( eq ) {
						return equate_abs(qcong.thm,*eq);
					}
				}
			}
			return {};
		}
	}
	return {};
}

Thm Rewriter::steps(Rules const& rules, CTerm const& source, unsigned int min, unsigned int max, vector<char> const& pos) const {
	Ctxt const& ctxt = source.ctxt();
	Thm lrefl = refl.weaken(ctxt);
	Thm ltrans = trans.weaken(ctxt).allE(source);
	Thm eq = lrefl.allE(source);
	auto begin = pos.begin(), end = pos.end();
	CTerm s = source;
	for( unsigned int i = 0; i < max; i++ ) {
		auto const& step = _step(rules,s,begin,end,lrefl);
		if( !step ) {
			if( i < min ) {
				throw TooFewSteps(source);
			} else {
				return eq;
			}
		}
		auto const& app = step->app();
		assert(app);
		CTerm const& t = app->second;
		Thm tr = ltrans.allE(s).allE(t).impE(eq);
		eq = tr.impE(*step);
		s = t;
	}
	return eq;
}
Thm Rewriter::rewrite(Rules const& rules, Thm const& source, unsigned int min, unsigned int max, vector<char> const& pos) const {
	Thm const& eq = steps(rules,source,min,max,pos);
	auto const& app = eq.app();
	assert(app);
	CTerm const& target = app->second;
	return imp.weaken(source.ctxt()).allE(source).allE(target).impE(eq).impE(source);
}
