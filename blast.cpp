#include "locale.hpp"
using namespace std;

CTerm dummy( Ctxt const& ctxt ) {
	return ctxt.cterm(DUMMY);
}

static Opt<Thm> _rule_applies( Thm const& rule, Ctxt& ctxt, Thm const& tmp, CTerm const& goal ) {
	auto const& m = match( rule, goal, [&](auto v){ return rule.ctxt().fixes(v); } );
	if( !m ) {
		return {};
	}
	auto intp = Intp(rule.ctxt(),ctxt);
	for(;;) {
		if( auto const& v = intp.fixing() ) {
			if( auto const& val = m->get(*v) ) {
				intp.instantiate(*val);
			} else {
				intp.instantiate(dummy(ctxt));
			}
		} else if( auto const& assm = intp.assuming() ) {
			intp.discharge(ctxt.assume(*assm));
		} else {
			break;
		}
	}
	return tmp.impE(intp.subst(rule)).intro();
}

Opt<Thm> rule_applies( Thm const& rule, Thm const& thesis ) {
	Ctxt ctxt = thesis.ctxt().branch();
	Thm tmp = thesis.weaken(ctxt);
	auto imp = tmp.cbinary(IMP);
	if( !imp ) {
		throw Error("#apply")(thesis);
	}
	return _rule_applies(rule,ctxt,tmp,imp->first);
}

Opt<Thm> rules_apply( set<Thm> const& rules, Thm const& thesis ) {
	Ctxt ctxt = thesis.ctxt().branch();
	Thm tmp = thesis.weaken(ctxt);
	if( auto imp = tmp.cbinary(IMP) ) {
		for( auto const& rule : rules ) {
			if( auto ret = _rule_applies(rule,ctxt,tmp,imp->first) ) {
				return ret;
			}
		}
	}
	return {};
}
Thm rules_apply( set<Thm> const& rules, Thm thesis, size_t min, size_t max, bool safe ) {
	for( int i = 0;; i++ ) {
		if( i == max ) {
			if( safe ) break;
			throw Error("\"apply limit exceeded\"")(to_string(max));
		}
		if( auto const& res = rules_apply(rules,thesis) ) {
			thesis = *res;
			continue;
		}
		if( i < min ) {
			throw Error("\"Rule not applicable\"");
		}
		break;
	}
	return thesis;
}
