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
			rule = ALL(*param /= rule);
			t = LAM(*param /= t);
		} else {
			throw Error(l);
		}
	}
	string thesis = avoid("thesis",[&](string const& x){ return ctxt.constant(x); });
	// proving the existence
	Ctxt prover = ctxt.branch();
	prover.fix(thesis);
	Thm thm = prover.assume( f &= rule >>= thesis );
	thm = thm.allE(t);
	thm = rewriter->rewrite(beta,thm,steps,steps,{0,1});
	thm = discharge(thm,rewriter->refl);
	thm = thm.intro();
	auto[x,props] = ctxt.obtain(thm);
	return {f,props[0]};
}

