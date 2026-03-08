#include "theory.hpp"
#include "inference.hpp"

using namespace std;

pair<string,Thm> Thy::define( Term const& eq/* f x... = r */, Opt<string const&> name ) & {
	auto app1 = eq.app();
	if( !app1 ) throw Error("\"unexpected definition\"")(eq);
	auto [eq1,r] = *app1;
	auto app2 = eq1.app();
	if( !app2 ) throw Error("\"unexpected definition\"")(eq);
	auto [relt,fxs] = *app2;
	auto rel = relt.sym();
	if( !rel ) throw Error("\"unexpected definition\"")(eq);
	auto [f,xs] = uncurry(fxs);
	unsigned int steps = 0;
	auto qeq = eq; // will be ∀x... f x... = r
	Term r_abs = r;// will be λx... r
	for( auto it = xs.rbegin(); it != xs.rend(); it++, steps++ ) {
		if( auto x = it->sym() ) {
			throw Error("\"unsupported functional definition\"")(fxs);
			qeq = *x &= qeq;
			//r_abs = LAM(*x /= r_abs);
		} else {
			throw Error(fxs);
		}
	}
	auto r_cabs = cterm(r_abs);// (λx... r) must be closed
	Thy lthy = branch();// will fix x...
	auto r_cabs_app = r_cabs.subst(*lthy.parent());// will be (λx... r) x...
	for( auto it = xs.begin(); it != xs.end(); it++ ) {
		auto x = it->sym();
		r_cabs_app = r_cabs_app(lthy.fix(*x));
	}
	// proving the existence
	string thesis = avoid("thesis",[&](string_view const& x){ return constant(x); });
	auto const& thesis_intp = fork();
	Ctxt thesis_ctxt = thesis_intp.ctxt();
	thesis_ctxt.fix(thesis);
	Thm thm = thesis_ctxt.assume( f &= qeq >>= thesis );// ∀f. (∀x... f x... = r) ⟹ thesis
	auto const& simp = lthy.rewriter(SIMP);
	auto inf = Resolver(simp);
//	simp.add_rewrite_rule(inf.rules,lthy.weaken(_beta),false);
	auto eq_thm = inf.steps(lthy,r_cabs_app,{},steps,steps,false,{},{*rel});// (λx... r) x... = r
	eq_thm = eq_thm.intro().subst(thesis_intp);// ∀x... (λx... r) x... = r
	thm = thm.allE(r_cabs.subst(thesis_intp));// (∀x... (λx... r) x... = r) ⟹ thesis
	thm = thm << eq_thm;// thesis
	thm = thm.intro();// ∀thesis. (∀f. (∀x... f x... = r) ⟹ thesis) ⟹ thesis
	auto [cf,spec] = obtain( f, thm, make_spec_name( name ? *name : f ), true );// f, ∀thesis. ((∀x... f x... = r) ⟹ thesis) ⟹ thesis
	auto imp_refl = [&]( auto&& loc ) {// _ ⟹ _
		return loc.assume(loc.fix("_")).intro();
	}(fork().ctxt());
	auto def_thm = spec << imp_refl;
	string def_name = (name ? *name : f) + "_def";
	add_thm(def_name,def_thm);
	return {def_name,def_thm};
}

