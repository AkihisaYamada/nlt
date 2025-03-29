#include "syntax.hpp"

using namespace std;

Syntax SYNTAX;

Syntax::Syntax() {
	infix("⟹",0,1,0);
	binder("∀",0,0);
	infix(".",-1,-1,-2);
}

function<ostream&(ostream&)> Syntax::pretty_term(Term const& term, int level) const & {
	return [this,&term,level](ostream& os) -> ostream& {
		if( auto sym = term.sym() ) {
			if( _prefixes.contains(*sym) || _binders.contains(*sym) || _infixes.contains(*sym) ) {
				return os << '(' << *sym << ')';
			}
			return os << *sym;
		} else if( auto app = term.app() ) {
			auto const& fun = app->first, arg = app->second;
			if( auto sym = fun.sym() ) {
				if( auto x = _prefixes.finds(*sym) ) {
					auto const& op = x->second;
					if( level > op.llevel ) {
						os << '(';
					}
					os << *sym << ' ' << pretty_term(arg,op.rlevel);
					if( level > op.llevel ) {
						os << ')';
					}
					return os;
				}
				if( auto abs = arg.bind() )
				if( auto x = _binders.finds(*sym) ) {
					auto const& op = x->second;
					if( level > op.llevel ) {
						os << '(';
					}
					os << *sym << ' ' << abs->first;
					Term cur = abs->second;
					while( auto abs2 = cur.binder(*sym) ) {
						os << ' ' << abs2->first;
						cur = abs2->second;
					}
					os << ". " << pretty_term(cur,op.rlevel);
					if( level > op.llevel ) {
						os << ')';
					}
					return os;
				}
			} else if( auto app_in = fun.app() ) {
				auto const& fun_in = app_in->first, arg_in = app_in->second;
				if( auto sym = fun_in.sym() ) {
					if( auto x = _prefixes.finds(*sym) ) {
						auto const& op = x->second;
						if( level > op.llevel ) {
							os << '(';
						}
						os << *sym << ' ';
						os << pretty_term(arg,op.rlevel);
						if( level > op.llevel ) {
							os << ')';
						}
						return os;
					}
					if( auto x = _infixes.finds(*sym) ) {
						auto const& op = x->second;
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
					if( auto abs = arg.bind() )
					if( auto x = _mid_binders.finds(*sym) ) {
						auto const& op = x->second;
						if( level > op.llevel ) {
							os << '(';
						}
						os << op.prefix << ' ' << abs->first << ' ' << op.mid << ' ' << pretty_term(arg_in,op.rlevel) << ". " << pretty_term(abs->second,level);
						if( level > op.llevel ) {
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
		} else if( auto abs = term.bind() ) {
			if( level > 0 ) {
				os << '(';
			}
			os << abs->first << ". " << pretty_term(abs->second, 0);
			if( level > 0 ) {
				os << ')';
			}
			return os;
		} else if( auto fix = term.unbind() ) {
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
	return [this,ctxt](ostream& os)->ostream& {
		function<void(ostream&,Term const&)> term = [this](ostream& os, Term const& t) {
			os << pretty_term(t);
		};
		for( int i = 0; i < ctxt.revision(); i++ ) {
			if( auto fix = ctxt.fixed(i) ) {
				os << "\tfixes " << *fix << ';' << std::endl;
			} else if( auto assume = ctxt.assumed(i) ) {
				os << "\tassumes " << pretty_term(*assume) << ';'<< std::endl;
			} else if( auto obtain = ctxt.obtained(i) ) {
				auto [sym,thm,spec] = *obtain;
				os << "\tobtains " << sym << "\n\t  where " << spec << ';' << std::endl;
			} else {
				assert(false);
			}
		}
		return os;
	};
}

function<ostream&(ostream&)> Syntax::pretty_subst(Subst const& subst) const & {
	static function<void(ostream&,std::pair<std::string const,Opt<Term>> const&)> pair = [this](ostream& os, auto p){
		auto t = p.second ? *p.second : p.first;
		os << pretty_term(p.first) << " := " << pretty_term(t);
	};
	return [&](ostream& os)->ostream&{
		os << "[ ";
		auto& map = subst.map();
		out_sep(os, map.begin(), map.end(), ",\n  ", pair );
		return os << " ]";
	};
}
