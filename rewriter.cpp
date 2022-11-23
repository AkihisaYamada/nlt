#include <iostream>
#include "util.hpp"

using namespace std;

Rewriter::Rules& Rewriter::Rules::add(Thm const& thm) {
	// checking well-formedness and extracting the lhs of the rewrite rule
	Ctxt loc = thm.ctxt().branch();
	Thm body = strip_all(thm,loc);
	auto const& app = body.app();
	if( !app.has_value() ) {
		throw Error(thm);
	}
	auto const& app2 = app->first.app();
	if( !app2.has_value() ) {
		throw Error(thm);
	}
	push_back({thm,app2->second});
	return *this;
}

optional<Thm> Rewriter::equate(Rules const& rules, CTerm const& haystack) const {
	for( auto const& rule : rules ) {
		auto const& pat = rule.pat;
		auto const& fsyms = pat.ctxt().syms();
		auto const& m = match(fsyms,pat,haystack);
		if( m.has_value() ) {
			// haystack = lθ
			Thm ret = rule.thm.weaken(haystack.ctxt()); // ret = ∀x... l = r
			for( auto const& var : pat.ctxt().sym_list() ) {
				ret = ret.allE(*m->get(var));
			}
			return ret; // lθ = rθ
		}
	}
	auto const& app = haystack.app();
	if( app.has_value() ) {
		auto const& fun = app->first, arg = app->second;
		auto const& opt1 = equate(rules,fun);
		if( opt1.has_value() ) {
			return
				discharge(fun_cong.weaken(opt1->ctxt()),*opt1) // ∀x. s x = t x
				.allE(arg);// s arg = t arg
		}
		auto const& opt2 = equate(rules,arg);
		if( opt2.has_value() ) {
			return
				discharge(arg_cong.weaken(opt2->ctxt()),*opt2) // ∀f. f s = f t
				.allE(fun);// fun s = fun t
		}
		return std::optional<Thm>();
	}
	auto const& abs = haystack.abs();
	if( abs.has_value() ) {
		auto const& var = abs->first;
		auto const& body = abs->second;
		auto const& opt = equate(rules,body);
		if( opt.has_value() ) {
			Thm all = opt->intro();// ∀x. s = t
			auto const& app = opt->app();
			CTerm const& s = app->first.app()->second.lift();// x. s
			CTerm const& t = app->second.lift();// x. t
			return ext.weaken(all.ctxt()).allE(s).allE(t).impE(all);// (x. s) = (x. t)
		}
	}
	return std::optional<Thm>();
}

optional<Thm> Rewriter::rewrite(Rules const& rules, Thm const& thm) const {
	auto const& eq = equate(rules,thm);
	if( eq.has_value() ) {
		return discharge(eq_imp.weaken(thm.ctxt()),*eq).impE(thm);
	}
	return optional<Thm>();
}
Thm Rewriter::normalize(Rules const& rules, Thm const& thm, unsigned int steps) const {
	if( steps == 0 ) {
		throw Error(Term("Exceeded limit"));
	}
	auto const& next = rewrite(rules,thm);
	if( next.has_value() ) {
		return normalize(rules,*next,steps-1);
	}
	return thm;
}