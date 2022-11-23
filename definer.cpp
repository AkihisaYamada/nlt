#include "util.hpp"

void Definer::define(Ctxt& ctxt, String const& sym, Term const& rule) const {
	Ctxt loc = ctxt.branch();
	CTerm eq = strip_all(rule,loc);
	auto const& app = eq.app();
	if( !app.has_value() ) {
		throw Error(eq);
	}
	auto const& app2 = app->first.app();
	if( !app2.has_value() || app2->first != EQ ) {
		throw Error(eq);
	}
	auto const& l = app2->first;
	auto const& r = app->first;
	auto pair = uncurry(l);
	Ctxt obtainer = ctxt.obtain(pair.first,{{"def",rule}});
}

