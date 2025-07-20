#include "definer.hpp"

using namespace std;

static Error const MalformedBeta = Error("#malformed-beta");
static Error const UnknownEq = Error("#unknown-equality");

Definer::_Init Definer::_init( Thy const& thy, Thm const& beta ) {
	auto const& [beta2,n,i] = strip_all(beta);// (λ α) x = α.[x]
	auto const& bin = strips_binary(beta2);// (λ _) _ = _
	if( !bin ) throw MalformedBeta(beta);
	auto const& [EQ,l,r] = *bin;
	auto const& ind = thy.rewriter().gets_rel_ind(EQ);
	if( !ind ) throw UnknownEq(beta);
	auto const& bin2 = strips_binary(l);// l: (λ _) _
	if( !bin2 ) throw MalformedBeta(beta);
	auto const& [LAM,abs,arg] = *bin2;
	auto const& refl = thy.rewriter().get_refl(*ind);
	return {thy,EQ,LAM,beta,refl};
}

pair<string,Thm> Definer::define(Thy& thy, Term const& fxs, Term const& r, Opt<string const&> name) const {
	auto [f,xs] = uncurry(fxs);
	auto eq = Term(EQ)(fxs)(r);// eq: f x... = r
	unsigned int steps = 0;
	auto qeq = eq; // will be ∀x... f x... = r
	Term r_abs = r;// will be λx... r
	for( auto it = xs.rbegin(); it != xs.rend(); it++, steps++ ) {
		if( auto x = it->sym() ) {
			qeq = *x &= qeq;
			r_abs = LAM(*x /= r_abs);
		} else {
			throw Error(fxs);
		}
	}
	auto r_cabs = thy.cterm(r_abs);// (λx... r) must be closed
	auto const& limport = thy.branch();
	Thy lthy = limport.thy();// will fix x...
	auto r_cabs_app = r_cabs.subst(limport);// will be (λx... r) x...
	for( auto it = xs.begin(); it != xs.end(); it++ ) {
		auto x = it->sym();
		r_cabs_app = r_cabs_app(lthy.fix(*x));
	}
	// proving the existence
	string thesis = avoid("thesis",[&](string_view const& x){ return thy.constant(x); });
	auto const& thesis_intp = thy.Ctxt::branch();
	Ctxt thesis_ctxt = thesis_intp.ctxt();
	thesis_ctxt.fix(thesis);
	Thm thm = thesis_ctxt.assume( f &= qeq >>= thesis );// ∀f. (∀x... f x... = r) ⟹ thesis
	auto eq_thm = lthy.rewriter().steps(beta,lthy,r_cabs_app,Rewriter::Ctrl{EQ,{},steps,steps,true});// (λx... r) x... = r
	eq_thm = eq_thm.intro().subst(thesis_intp);// ∀x... (λx... r) x... = r
	thm = thm.instantiate(r_cabs.subst(thesis_intp));// (∀x... (λx... r) x... = r) ⟹ thesis
	thm = thm << eq_thm;// thesis
	thm = thm.intro();// ∀thesis. (∀f. (∀x... f x... = r) ⟹ thesis) ⟹ thesis
	auto [cf,spec] = thy.obtain( f, thm, make_spec_name( name ? *name : f ) );// f, ((∀x... f x... = r) ⟹ thesis) ⟹ thesis
	return {f,spec};
}

