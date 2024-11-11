#include "syntax.hpp"

using namespace std;

Syntax SYNTAX;

Syntax::Syntax() {
	infix("⟹",0,1,0);
	prefix("∀",0,0);
}

function<ostream&(ostream&)> Syntax::pretty_term(Term const& term, int level) const & {
	return [this,&term,level](ostream& os) -> ostream& {
		if( auto sym = term.sym() ) {
			if( _prefixes.contains(*sym) || _infixes.contains(*sym) ) {
				return os << '(' << *sym << ')';
			}
			return os << *sym;
		} else if( auto app = term.app() ) {
			auto const& fun = app->first, arg = app->second;
			if( auto sym = fun.sym() ) {
				if( auto it = _prefixes.find(*sym); it != _prefixes.end() ) {
					auto const& op = it->second;
					if( level > op.llevel ) {
						os << '(';
					}
					os << *sym << ' ' << pretty_term(arg,op.rlevel);
					if( level > op.llevel ) {
						os << ')';
					}
					return os;
				}
			} else if( auto app_in = fun.app() ) {
				auto const& fun_in = app_in->first, arg_in = app_in->second;
				if( auto sym = fun_in.sym() ) {
					auto it = _infixes.find(*sym);
					if( it != _infixes.end() ) {
						auto const& op = it->second;
						if( level > op.level ) {
							os << '(';
						}
						os << pretty_term(arg_in,op.llevel);
						os << ' ' << *sym << ' ';
						os << pretty_term(arg,op.rlevel);
						if( level > op.level ) {
							os << ')';
						}
						return os;
					}
				}
			}
			if( level >= 1000 ) {
				os << '(';
			}
			os << pretty_term(fun, 999) << ' ';
			os << pretty_term(arg, 1000);
			if( level >= 1000 ) {
				os << ')';
			}
			return os;
		} else if( auto abs = term.abs() ) {
			return os << abs->first << ". " << pretty_term(abs->second, 0);
		} else if( auto fix = term.fix() ) {
			return os << fix->first << ".[" << pretty_term(fix->second) << ']';
		} else {
			assert(false);
		}
	};
}

function<ostream&(ostream&)> Syntax::pretty_cterm(CTerm const& t) const & {
	return [this,t](ostream& os) -> ostream& {
		return (_print_ctxt ? os << '@' << t.ctxt().id() << ' ' : os) << pretty_term(t);
	};
}
function<ostream&(ostream&)> Syntax::pretty_thm(Thm const& t) const & {
	return pretty_cterm(t);
}

function<ostream&(ostream&)> Syntax::pretty_thms(StrMap<Thm> const& thms) const & {
	return [this,&thms](ostream& os) -> ostream& {
		for( auto const& thm : thms ) {
			os << "  thm " << thm.first << ": " << pretty_term(thm.second) << endl;
		}
		return os;
	};
}

function<ostream&(ostream&)> Syntax::pretty_ctxt(Ctxt const& ctxt) const & {
	return [this,ctxt](ostream& os) -> ostream& {
		function<void(ostream&,Term const&)> term = [this](ostream& os, Term const& t) {
			os << pretty_term(t);
		};
		for( int i = 0; i < ctxt.revision(); i++ ) {
			if( auto fix = ctxt.fixed(i) ) {
				os << "\tfixes " << *fix << ';' << std::endl;
			} else if( auto assume = ctxt.assumed(i) ) {
				os << "\tassumes " << pretty_term(*assume) << ';'<< std::endl;
			} else if( auto obtain = ctxt.obtained(i) ) {
				auto [sym,thm] = *obtain;
				os << "\tobtains " << sym << "\n\t  where ";
				auto all1 = thm.binder(ALL); // ∀thesis. (∀sym. p_1 ⟹ ... ⟹ p_n ⟹ thesis) ⟹ thesis
				assert(all1);
				auto imp1 = all1->second.binary(IMP); // (∀sym. p_1 ⟹ ... ⟹ p_n ⟹ thesis) ⟹ thesis
				auto all2 = imp1->first.binder(ALL);// ∀sym. p_1 ⟹ ... ⟹ p_n ⟹ thesis
				assert(all2);
				auto [sym2,imps] = *all2;
				auto imp = imps.binary(IMP);
				assert(imp);
				auto spec = imp->first;
				imps = imp->second;
				os << spec;
				for(;;) {
					auto imp2 = imps.binary(IMP);
					if( !imp2 ) break;
					os << "\n\t    and " << imp2->first;
					imps = imp2->second;
				}
				os << ';' << std::endl;
			} else {
				assert(false);
			}
		}
		return os;
	};
}

function<ostream&(ostream&)> Syntax::pretty_subst(CSubst const& subst) const & {
	static function<void(ostream&,std::pair<std::string const,Term> const&)> pair = [this](ostream& os, auto p){
		os << pretty_term(p.first) << " := " << pretty_term(p.second);
	};
	return [&](ostream& os)->ostream&{
		os << "[ ";
		auto& map = subst.map();
		out_sep(os, map.begin(), map.end(), ",\n  ", pair );
		return os << " ]";
	};
}
