#include "util.hpp"

using namespace std;

void Definer::define(Ctxt& ctxt, Term const& rule, optional<String const> name) const {
	Ctxt loc = ctxt.branch();
	Term eq = strip_all(rule,loc);
	auto const& app = eq.app();
	if( !app.has_value() ) {
		throw Error(eq);
	}
	auto const& app2 = app->first.app();
	if( !app2.has_value() || app2->first != EQ ) {
		throw Error(eq);
	}
	auto const& l = app2->second;
	Term r = app->second;
	auto pair = uncurry(l);
	String const& sym = pair.first;
	Ctxt obtainer = ctxt.obtain(pair.first,
		{{(string)(name.has_value() ? *name : sym) +".def",rule}}
	);
	// existence proving
	Ctxt prover = ctxt.branch();
	String thesis = avoid("thesis",[&](String const& x){ return ctxt.find_sym(x).has_value(); });
	prover.fix(thesis);
	prover.assume( "assm", ALL( sym /= rule >>= thesis ) );
	// building the lambda term
	unsigned int steps = 0;
	for( auto it = pair.second.rbegin(); it != pair.second.rend(); it++, steps++ ) {
		auto const& param = it->sym();
		if( !param.has_value() ) {
			throw Error(l);
		}
		r = LAM(*param /= r);
	}
	Thm thm = prover.thm("assm");
	thm = thm.allE(r);
	thm = rewriter->normalize(beta,thm,steps);
	thm = discharge(thm,rewriter->refl);
	thm = thm.intro();
	ctxt.import(obtainer.interpret(ctxt,{thm}));
}

