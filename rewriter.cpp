#include <iostream>
#include "util.hpp"

using namespace std;

Rewriter::Rules& Rewriter::Rules::add(Thm const& thm) {
	// checking well-formedness and extracting the lhs of the rewrite rule
	Ctxt loc = thm.ctxt().branch();
	Thm body = strip_all(thm,loc);
	auto const& app = body.app();
	if( !app.has_value() ) {
		throw Error(thm);
	}
	auto const& app2 = app->first.app();
	if( !app2.has_value() ) {
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
	CTerm const& s = app->first.app()->second.lift();// x. s
	CTerm const& t = app->second.lift();// x. t
	return ext.weaken(all.ctxt()).allE(s).allE(t).impE(all);// (x. s) = (x. t)
}


static Thm equate_quantified(Thm const& ext, Thm const& eq) {
	Thm all = eq.intro();// ∀x. s = t
	auto const& app = eq.app();
	CTerm const& s = app->first.app()->second.lift();// x. s
	CTerm const& t = app->second.lift();// x. t
	return ext.weaken(all.ctxt()).allE(s).allE(t).impE(all);// (ξ x. s) = (ξ x. t)
}

optional<Thm> Rewriter::_step(Rules const& rules, CTerm const& source, Thm const& refl) const {
	for( auto const& rule : rules ) {
		auto const& pat = rule.pat;
		auto const& fvars = pat.ctxt().fvars();
		auto const& m = match(fvars,pat,source);
		if( m.has_value() ) {
			// source = lθ
			Thm ret = rule.thm.weaken(source.ctxt());// ret = ∀x... l = r
			for( auto const& var : pat.ctxt().fvar_list() ) {
				ret = ret.allE(*m->get(var));
			}
			return ret; // lθ = rθ
		}
	}
	for( auto const& cong : congs ) {
		auto const& pat = cong.pat;
		auto const& fvars = pat.ctxt().fvars();
		auto const& m = match(fvars,pat,source);
		if( m.has_value() ) {// source = C[s...]
			Thm ret = cong.thm.weaken(source.ctxt());// ret = ∀x. ∀x'. x = x' ⟹ ... ⟹ C[x...] = C[x'...]
			auto const& fvar_list = pat.ctxt().fvar_list();
			auto it = fvar_list.begin();
			auto end = fvar_list.end();
			for(;;) {
				auto const& si = *m->get(*it);
				it++;
				auto const& eq_opt = _step(rules,si,refl);
				if( eq_opt.has_value() ) {
					ret = discharge(ret,*eq_opt);
					break;
				}
				if( it == end ) {
					return optional<Thm>();
				}
				ret = discharge(ret,refl.allE(si));
			}
			for( ; it != end; it++ ) {
				ret = discharge(ret,refl.allE(*m->get(*it)));
			}
			return ret;
		}
	}
	for( auto const& qcong : quantifier_congs ) {
		auto const& pat = qcong.pat;
		Ctxt const& ctxt = pat.ctxt();
		auto const& m = match(ctxt.fvars(),pat,source);
		if( m.has_value() ) {// source = (ξ) α
			for( auto const& var : ctxt.fvar_list() ) {// shouldn't loop more than once
				auto const& s = m->get(var);
				auto const& abs = s->abs();
				if( abs.has_value() ) {
					CTerm const& s = abs->second;
					auto const& eq_opt = _step(rules,s,refl.weaken(s.ctxt()));
					if( eq_opt.has_value() ) {
						return equate_abs(qcong.thm,*eq_opt);
					}
				}
			}
			return optional<Thm>();
		}
	}
	return std::optional<Thm>();
}

optional<Thm> Rewriter::_step(Rules const& rules, CTerm const& source, vector<char>::const_iterator pos_it, vector<char>::const_iterator pos_end, Thm const& refl) const {
	if( pos_it == pos_end ) {// rewritable position
		return _step(rules,source,refl);
	}
	for( auto const& cong : congs ) {
		auto const& pat = cong.pat;
		auto const& fvars = pat.ctxt().fvars();
		auto const& fvar_list = pat.ctxt().fvar_list();
		auto const& m = match(fvars,pat,source);
		if( m.has_value() ) {// source = C[s...]
			Thm ret = cong.thm.weaken(source.ctxt());// ret = ∀x. ∀x'. x = x' ⟹ ... ⟹ C[x...] = C[x'...]
			auto var_it = fvar_list.begin();
			auto var_end = fvar_list.end();
			char i = 0;
			for(;;) {
				auto const& var = *var_it;
				var_it++;
				auto const& si = *m->get(var);
				if( *pos_it == i ) {
					pos_it++;
					auto const& eq_opt = _step(rules,si,pos_it,pos_end,refl);
					if( eq_opt.has_value() ) {
						ret = discharge(ret,*eq_opt);
						break;
					}
					return optional<Thm>();
				}
				if( var_it == var_end ) {
					return optional<Thm>();
				}
				ret = discharge(ret,refl.allE(si));
				i++;
			}
			for( ; var_it != var_end; var_it++ ) {
				ret = discharge(ret,refl.allE(*m->get(*var_it)));
			}
			return ret;
		}
	}
	for( auto const& qcong : quantifier_congs ) {
		auto const& pat = qcong.pat;
		Ctxt const& ctxt = pat.ctxt();
		auto const& m = match(ctxt.fvars(),pat,source);
		if( m.has_value() ) {// source = (ξ) α
			for( auto const& var : ctxt.fvar_list() ) {// shouldn't loop more than once
				auto const& s = m->get(var);
				auto const& abs = s->abs();
				if( abs.has_value() ) {
					pos_it++;
					auto const& eq_opt = _step(rules,abs->second,pos_it,pos_end,refl);
					if( eq_opt.has_value() ) {
						return equate_abs(qcong.thm,*eq_opt);
					}
				}
			}
			return optional<Thm>();
		}
	}
	return std::optional<Thm>();
}

Thm Rewriter::steps(Rules const& rules, CTerm const& source, unsigned int n, std::vector<char> const& pos) const {
	Ctxt const& ctxt = source.ctxt();
	Thm lrefl = refl.weaken(ctxt);
	Thm ltrans = trans.weaken(ctxt).allE(source);
	Thm eq = lrefl.allE(source);
	auto begin = pos.begin(), end = pos.end();
	CTerm s = source;
	for( unsigned int i = 0; i < n; i++ ) {
		auto const& step = _step(rules,s,begin,end,lrefl);
		if( !step.has_value() ) {
			break;
		}
		CTerm const& t = step->app()->second;
		Thm tr = ltrans.allE(s).allE(t).impE(eq);
		eq = tr.impE(*step);
		s = t;
	}
	return eq;
}
Thm Rewriter::rewrite(Rules const& rules, Thm const& source, unsigned int n, std::vector<char> const& pos) const {
	Thm const& eq = steps(rules,source,n,pos);
	CTerm const& target = eq.app()->second;
	return imp.weaken(source.ctxt()).allE(source).allE(target).impE(eq).impE(source);
}
