#include "definer.hpp"

using namespace std;

static Error const MalformedBeta = Error("#malformed-beta");
static Error const UnknownEq = Error("#unknown-equality");

Definer::_Init Definer::_init( Locale const& loc, Thm const& beta ) {
	auto const& beta2 = strip_all(beta).first;// (λ α) x = α.[x]
	auto const& bin = strips_binary(beta2);// (λ _) _ = _
	if( !bin ) throw MalformedBeta(beta);
	auto const& [EQ,l,r] = *bin;
	auto const& ind = loc.rewriter().gets_rel_ind(EQ);
	if( !ind ) throw UnknownEq(beta);
	auto const& bin2 = strips_binary(l);// l: (λ _) _
	if( !bin2 ) throw MalformedBeta(beta);
	auto const& [LAM,abs,arg] = *bin2;
	auto const& refl = loc.rewriter().get_refl(*ind);
	return {loc,EQ,LAM,beta,refl};
}

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
	auto sub = loc.branch();
	sub.fix(thesis);
	Thm thm = sub.assume( f &= rule >>= thesis );// (∀f x... l = r) ⟹ thesis
	thm = thm.instantiate(t);// (∀x... l[f:=t] = r) ⟹ thesis
	thm = _loc.rewriter().rewrite(beta,sub,thm,Rewriter::Ctrl{EQ,{0,1},steps,steps,true});// (∀x... r = r) ⟹ thesis
	thm = thm << refl.weaken(sub);// thesis
	thm = thm.intro();// ((∀f x... l = r) ⟹ thesis) ⟹ thesis
	auto [cf,spec] = loc.obtain( f, thm, make_spec_name( name ? *name : f ) );// f, ((∀x... l = r) ⟹ thesis) ⟹ thesis
	return {f,spec};
}

