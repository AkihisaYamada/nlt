#include "util.hpp"

CTerm Rewriter::rule2pat(Thm const& thm) {
	Ctxt loc = thm.ctxt().branch();
	Thm body = strip_all(thm,loc);
	auto const& app = body.app();
	if( !app.has_value() ) {
		throw MalformedRewrite(thm);
	}
	auto const& app2 = app->first.app();
	if( !app2.has_value() ) {
		throw MalformedRewrite(thm);
	}
	return app2->second;
}
std::optional<Thm> Rewriter::apply(Thm const& thm) {
	Ctxt loc = thm.ctxt().branch();
	Thm const& stripped_thm = strip_all(thm,loc);
	return apply(stripped_thm,loc.branch().enclose(BOX),stripped_thm);
}

std::optional<Thm> Rewriter::apply(Thm const& stripped_thm, CTerm const& context, CTerm const& s) const {
	for( auto const& rule : rules ) {
		auto const& pat = rule.pat;
		auto const& fsyms = pat.ctxt().syms();
		auto const& m = match(fsyms,pat,s);
		if( m.has_value() ) {
			// s = lθ
			Ctxt ctxt = stripped_thm.ctxt();
			Thm eq = rule.thm.weaken(ctxt); // eq = ∀x... l = r
			for( auto const& var : pat.ctxt().sym_list() ) {
				eq = eq.allE(*m->get(var));
			}
			// now eq is lθ = rθ and thm = C[lθ]. We return C[rθ]
			return EQ_mono.allE(context.lift()).impE(eq).impE(stripped_thm).intro();
		}
	}
	auto const& app = s.app();
	if( !app.has_value() ) {
		return std::optional<Thm>();
	}
	auto const& fun = app->first, arg = app->second;
	auto const& opt = apply(stripped_thm,context(arg),fun);
	if( opt.has_value() ) {
		return opt;
	}
	return apply(stripped_thm,fun(context),arg);
}

