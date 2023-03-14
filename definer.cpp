#include "util.hpp"

using namespace std;

void Definer::define(Ctxt& ctxt, Term const& l, Term const& r, optional<String> const& name) const {
	auto unc = uncurry(l);
	String const& f = unc.first;
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
	auto const& pair = ctxt.obtain(f,{{ *(name ? *name : f) + ".def", rule }});
	Ctxt const& obtainer = pair.second;
	// proving the existence
	Ctxt prover = ctxt.branch();
	String thesis = avoid("thesis",[&](String const& x){ return (bool)ctxt.find_sym(x); });
	prover.fix(thesis);
	prover.assume( "assm", ALL( f /= rule >>= thesis ) );
	Thm thm = prover.thm("assm");
	thm = thm.allE(t);
	thm = rewriter->rewrite(beta,thm,steps,steps,{0,1});
	thm = discharge(thm,rewriter->refl);
	thm = thm.intro();
	ctxt.import(obtainer.interpret(ctxt,{thm}));
}

