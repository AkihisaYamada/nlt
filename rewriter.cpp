#include <iostream>
#include "rewriter.hpp"

using namespace std;

Rewriter::Rules& Rewriter::Rules::add(Thm const& thm) {
	// checking well-formedness and extracting the lhs of the rewrite rule
	Ctxt loc = thm.ctxt().branch();
	Thm body = strip_all(thm,loc);
	auto const& app = body.capp();
	if( !app ) {
		throw Error(thm);
	}
	auto const& app2 = app->first.capp();
	if( !app2 ) {
		throw Error(thm);
	}
	push_back({app2->second,body});
	return *this;
}

static Thm equate_cong(Thm const& cong, Thm const& eq, CTerm const& arg) {
	return (cong.weaken(eq.ctxt()) << eq) // ∀x. s x = t x
			.allE(arg);// s arg = t arg
}

static Thm equate_abs(Thm const& thm, Thm const& eq) {
	// thm: ∀α. ∀β. (∀x. α.[x] = β.[x]) ⟹ α = β
	// eq: s = t
	CTerm s = eq.capp()->first.capp()->second;
	CTerm t = eq.capp()->second;
	Thm all = eq.intro();// ∀x. s = t
	CTerm dummy = all.capp()->first;
	Thm rule = make_rule(thm);// fix α β; assume ∀x. α.[x] = β.[x]; ⊢ α = β
	auto intp = Intp::make(rule.ctxt(),all.ctxt());
	intp.instantiate(s.lift(dummy).capp()->second);// α ← x. s
	intp.instantiate(t.lift(dummy).capp()->second);// β ← x. t
	intp.discharge(all);
	return intp.subst(rule); // (x. s) = (x. t)
}

Opt<Thm> Rewriter::_step(Rules const& rules, CTerm const& source, Thm const& refl) const {
	for( auto const& rule : rules ) {
		Ctxt const& rule_ctxt = rule.pat.ctxt();
		if( auto const& m = match(rule_ctxt.fvars(),rule.pat,source) ) {
			// source: l[m]
			Intp intp = Intp::make(rule_ctxt,source.ctxt());
			for( int i = 0; i < rule_ctxt.revision(); i++ ) {
				auto v = rule_ctxt.fixed(i);
				assert(v);
				intp.instantiate(*m->get(*v));
			}
			return intp.subst(rule.thm); // l[m] = r[m]
		}
	}
	for( auto const& cong : congs ) {
		Ctxt const& ctxt = cong.pat.ctxt();
		if( auto const& m = match(ctxt.fvars(),cong.pat,source) ) {// source: C[s...]
			Thm ret = cong.thm.weaken(source.ctxt());
			// ret: ∀x. ∀x'. x = x' ⟹ ... ⟹ C[x...] = C[x'...]
			size_t i = 0, n = ctxt.revision();
			for(;;) {
				auto v = ctxt.fixed(i);
				auto const& si = m->get(*v);
				assert(si);
				i++;
				if( auto const& eq = _step(rules,*si,refl) ) {
					ret = ret << *eq;
					break;
				}
				if( i == n ) {
					return {};
				}
				ret = ret << refl.allE(*si);
			}
			for( ; i < n; i++ ) {
				auto v = ctxt.fixed(i);
				ret = ret << refl.allE(*m->get(*v));
			}
			return ret;
		}
	}
	for( auto const& qcong : quantifier_congs ) {
		Ctxt const& ctxt = qcong.pat.ctxt();
		assert( ctxt.revision() == 1 ); // should have exactly one variable
		if( auto const& m = match(ctxt.fvars(),qcong.pat,source) ) {// source: (ξ)x. α.[x]
			auto const& val = m->get(*ctxt.fixed(0));
			assert(val);
			if( auto const& abs = val->cabs() ) {
				CTerm const& body = abs->second;
				if( auto const& eq = _step(rules,body,refl.weaken(body.ctxt())) ) {
					return equate_abs(qcong.thm,*eq);
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
			auto var_i = 0;
			auto var_end = ctxt.revision();
			assert( var_i != var_end );
			char i = 0;
			for(;;) {
				auto const& si = m->get(*ctxt.fixed(var_i));
				assert(si);
				var_i++;
				if( *pos_it == i ) {// rewrite step must occur inside this position
					pos_it++;
					if( auto const& eq = _step(rules,*si,pos_it,pos_end,refl) ) {
						// rewrite step was successful
						ret = discharge(ret,*eq);
						break;
					}
					return {};// no rewrite step was done
				} else if( var_i == var_end ) {
					return {};
				} else {
					ret = discharge(ret,refl.allE(*si));
					i++;
				}
			}
			for( ; var_i != var_end; var_i++ ) {// remaining variables are instantiated as is
				ret = discharge(ret,refl.allE(*m->get(*ctxt.fixed(var_i))));
			}
			return ret;
		}
	}
	for( auto const& qcong : quantifier_congs ) {
		Ctxt const& ctxt = qcong.pat.ctxt();
		assert( ctxt.revision() == 1 );
		if( auto const& m = match(ctxt.fvars(),qcong.pat,source) ) {// source: ξx. α.[x]
			auto const& val = m->get(*ctxt.fixed(0));
			assert(val);
			if( auto const& abs = val->cabs() ) {
				auto const& body = abs->second;
				pos_it++;
				if( auto const& eq = _step(rules,body,pos_it,pos_end,refl.weaken(body.ctxt())) ) {
					return equate_abs(qcong.thm,*eq);
				}
			}
			return {};
		}
	}
	return {};
}

Thm Rewriter::steps(Rules const& rules, CTerm const& source, unsigned int min, unsigned int max, bool safe, vector<char> const& pos) const {
	Ctxt const& ctxt = source.ctxt();
	Thm lrefl = refl.weaken(ctxt);// P ⟺ P
	Thm eq = lrefl.allE(source);// eq: source ⟺ source
	Thm ltrans = trans.weaken(ctxt).allE(source);
	auto begin = pos.begin(), end = pos.end();
	CTerm s = source;
	for( unsigned int i = 0;; i++ ) {
		if( i == max ) {
			if( safe ) break;
			throw Error("\"rewrite limit exceeded\"")(to_string(max));
		}
		auto const& step = _step(rules,s,begin,end,lrefl);
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
	return eq;
}
Thm Rewriter::rewrite(Rules const& rules, Thm const& source, unsigned int min, unsigned int max, bool safe, vector<char> const& pos) const {
	Thm const& eq = steps(rules,source,min,max,safe,pos);
	auto const& app = eq.capp();
	assert(app);
	CTerm const& target = app->second;
	return imp.weaken(source.ctxt()).allE(source).allE(target).impE(eq).impE(source);
}
