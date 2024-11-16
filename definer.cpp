#include "definer.hpp"

using namespace std;

pair<string,Thm> Definer::define(Ctxt& ctxt, Term const& l, Term const& r) const {
	auto unc = uncurry(l);
	string const& f = unc.first;
	// building the rule and the lambda term for f
	Term rule = Term(EQ)(l)(r);
	unsigned int steps = 0;
	Term t = r;
	for( auto it = unc.second.rbegin(); it != unc.second.rend(); it++, steps++ ) {
		if( auto param = it->sym() ) {
			rule = *param &= rule;
			t = LAM(*param /= t);
		} else {
			throw Error(l);
		}
	}
	// rule: ∀x... l = r,  t: λx... l
	string thesis = avoid("thesis",[&](string const& x){ return ctxt.constant(x); });
	// proving the existence
	Ctxt sub = ctxt.branch();
	sub.fix(thesis);
	Thm thm = sub.assume( f &= rule >>= thesis );// (∀f x... l = r) ⟹ thesis
	thm = thm.allE(t);// (∀x... l[f:=t] = r) ⟹ thesis
	thm = rewriter->rewrite(beta,thm,steps,steps,{0,1});// (∀x... r = r) ⟹ thesis
	thm = thm << rewriter->refl;// thesis
	thm = thm.intro();// ((∀f x... l = r) ⟹ thesis) ⟹ thesis
	auto [cf,spec] = ctxt.obtain(f,thm);// f, ((∀x... l = r) ⟹ thesis) ⟹ thesis
	return {f,spec};
}

