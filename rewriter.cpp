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

static Thm equate_cong(Thm const& cong, Thm const& eq, CTerm const& arg) {
	return discharge(cong.weaken(eq.ctxt()),eq) // ∀x. s x = t x
			.allE(arg);// s arg = t arg
}

static Thm equate_abs(Thm const& ext, Thm const& eq) {
	Thm all = eq.intro();// ∀x. s = t
	auto const& app = eq.app();
	CTerm const& s = app->first.app()->second.lift();// x. s
	CTerm const& t = app->second.lift();// x. t
	return ext.weaken(all.ctxt()).allE(s).allE(t).impE(all);// (x. s) = (x. t)
}


optional<Thm> Rewriter::equate(
	Rules const& rules, CTerm const& haystack, vector<bool>::const_iterator it, vector<bool>::const_iterator end
) const {
	if( it == end ) {
		return equate(rules,haystack);
	}
	bool i = *it;
	it++;
	auto const& app = haystack.app();
	if( app.has_value() ) {
		if( i ) {
			auto const& opt = equate(rules,app->second,it,end);
			if( opt.has_value() ) {
				return equate_cong(arg_cong,*opt,app->first);// fun s = fun t
			}
		} else {
			auto const& opt = equate(rules,app->first,it,end);
			if( opt.has_value() ) {
				return equate_cong(fun_cong,*opt,app->second);// s arg = t arg
			}
		}
	} else {
		auto const& abs = haystack.abs();
		if( abs.has_value() ) {
			auto const& opt = equate(rules,abs->second,it,end);
			if( opt.has_value() ) {
				return equate_abs(ext,*opt);
			}
		}
	}
	return optional<Thm>();
}
optional<Thm> Rewriter::equate(Rules const& rules, CTerm const& haystack) const {
	for( auto const& rule : rules ) {
		auto const& pat = rule.pat;
		Ctxt const& ctxt = pat.ctxt();
		auto const& fvars = ctxt.fvars();
		auto const& m = match(fvars,pat,haystack);
		if( m.has_value() ) {
			// haystack = lθ
			Thm ret = rule.thm.weaken(haystack.ctxt()); // ret = ∀x... l = r
			for( auto const& var : ctxt.fvar_list() ) {
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
			return equate_cong(fun_cong,*opt1,arg);// s arg = t arg
		}
		auto const& opt2 = equate(rules,arg);
		if( opt2.has_value() ) {
			return equate_cong(arg_cong,*opt2,fun);// fun s = fun t
		}
		return std::optional<Thm>();
	}
	auto const& abs = haystack.abs();
	if( abs.has_value() ) {
		auto const& opt = equate(rules,abs->second);
		if( opt.has_value() ) {
			return equate_abs(ext,*opt);
		}
	}
	return std::optional<Thm>();
}

optional<Thm> Rewriter::rewrite(Rules const& rules, Thm const& thm, vector<bool> const& pos) const {
	auto const& eq = equate(rules,thm,pos);
	if( eq.has_value() ) {
		return discharge(eq_prop1.weaken(thm.ctxt()),*eq).impE(thm);
	}
	return optional<Thm>();
}
Thm Rewriter::normalize(Rules const& rules, Thm const& thm, unsigned int steps, std::vector<bool> const& pos) const {
	Thm acc = thm;
	for( unsigned int i = 0; ; i++ ) {
		auto const& next = rewrite(rules,acc,pos);
		if( !next.has_value() ) {
			return acc;
		}
		acc = *next;
		if( i >= steps ) {
			return acc;
		}
	}
}