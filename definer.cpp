#include "definer.hpp"

using namespace std;

pair<string,Thm> Definer::define(Locale& loc, Term const& l, Term const& r, Opt<string const&> name) const {
	auto [f,args] = uncurry(l);
	// building the rule and the lambda term for f
	Term rule = Term(EQ)(l)(r);
	unsigned int steps = 0;
	Term t = r;
	for( auto it = args.rbegin(); it != args.rend(); it++, steps++ ) {
		if( auto param = it->sym() ) {
			rule = *param &= rule;
			t = LAM(*param /= t);
		} else {
			throw Error(l);
		}
	}
	// rule: ∀x... l = r,  t: λx... l
	string thesis = avoid("thesis",[&](string const& x){ return loc.constant(x); });
	// proving the existence
	Ctxt sub = loc.Ctxt::branch();
	sub.fix(thesis);
	Thm thm = sub.assume( f &= rule >>= thesis );// (∀f x... l = r) ⟹ thesis
	thm = thm.allE(t);// (∀x... l[f:=t] = r) ⟹ thesis
	thm = rewriter->rewrite(beta,thm,steps,steps,true,{0,1});// (∀x... r = r) ⟹ thesis
	thm = thm << rewriter->refl;// thesis
	thm = thm.intro();// ((∀f x... l = r) ⟹ thesis) ⟹ thesis
	auto [cf,spec] = loc.obtain( f, thm, make_spec_name( name ? *name : f ) );// f, ((∀x... l = r) ⟹ thesis) ⟹ thesis
	return {f,spec};
}

