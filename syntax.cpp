#include "syntax.hpp"

using namespace std;

function<ostream&(ostream&)> Syntax::pretty_term(Term const& term, int level) const {
	return [&](ostream& os) -> ostream& {
		auto const& sym = term.sym();
		if( sym.has_value() ) {
			if( prefixes.contains(*sym) || infixes.contains(*sym) ) {
				return os << '(' << *sym << ')';
			}
			return os << *sym;
		}
		auto const& app = term.app();
		if( app.has_value() ) {
			auto const& fun = app->first, arg = app->second;
			auto const& sym = fun.sym();
			if( sym.has_value() ) {
				auto it = prefixes.find(*sym);
				if( it != prefixes.end() ) {
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
			} else {
				auto const& app_in = fun.app();
				if( app_in.has_value() ) {
					auto const& fun_in = app_in->first, arg_in = app_in->second;
					auto const& sym = fun_in.sym();
					if( sym.has_value() ) {
						auto it = infixes.find(*sym);
						if( it != infixes.end() ) {
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
		}
		auto const& abs = term.abs();
		if( abs.has_value() ) {
			return os << abs->first << ". " << pretty_term(abs->second, 0);
		}
		auto const& fix = term.fix();
		if( fix.has_value() ) {
			return os << fix->first << ".[" << pretty_term(fix->second) << ']';
		}
		assert(false);
	};
}

function<ostream&(ostream&)> Syntax::pretty_thm(Thm const& thm) const {
	return [&](ostream& os) -> ostream& {
		return os << pretty_term(thm);
	};
}

function<ostream&(ostream&)> Syntax::pretty_thms(StrMap<Thm> const& thms) const {
	return [&](ostream& os) -> ostream& {
		for( auto const& thm : thms ) {
			os << "  thm " << thm.first << ": " << pretty_term(thm.second) << endl;
		}
		return os;
	};
}

function<ostream&(ostream&)> Syntax::pretty_ctxt(Ctxt const& ctxt) const {
	return [&](ostream& os) -> ostream& {
		os << "ctxt {" << endl;
		for( auto const& sym : ctxt.sym_list() ) {
			os << "  sym " << sym << endl;
		}
		for( auto const& assm : ctxt.assms() ) {
			os << "  assm " << pretty_term(assm) << endl;
		}
		for( auto const& thm : ctxt.thms() ) {
			os << "  thm " << thm.first << ": " << pretty_term(thm.second) << endl;
		}
		os << "}" << endl;
		return os;
	};
}

optional<string> Syntax::gets_thm_name() {
	switch( next_token_type() ) {
		case Lexer::Word: break;
		case Lexer::Number: return get_token();
		default: return optional<string>();
	}
	string ret = get_token();
	for(;;) {
		if( !skips('.') ) {
			return ret;
		}
		ret += '.';
		if( next_token_type() != Lexer::Word ) {
			return ret;
		}
		ret += get_token();
	}
}
string Syntax::get_thm_name() {
	auto const& opt = gets_thm_name();
	if( !opt.has_value() ) {
		throw Error("Required a theorem name");
	}
	return *opt;
}

optional<Term> Syntax::gets_term(int level) {
	if( !readable() ) {
		return optional<Term>();
	}
	Term ret;
	if( skips('(') ) {
		ret = gets_term(0).value();
		skip(')');
	} else {
		string_view sym = peek_token();
		auto it = prefixes.find(sym);
		if( it != prefixes.end() ) {
			if( it->second.llevel < level ) {
				return optional<Term>();
			}
			ret = Term(it->first);
			ignore_token();
			auto const& r = gets_term(it->second.rlevel);
			if( r.has_value() ) {
				ret = ret(r.value());
			}
		} else {
			String sym = get_token();
			if( skips('.') ) {
				auto const& t = gets_term(level);
				if( t.has_value() ) {
					ret = sym /= t.value();
				}
			} else if( skips('[') ) {
				ret = sym / gets_term(0).value();
				skip(']');
			} else {
				ret = Term(sym);
			}
		}
	}
	for(;;) {
		string_view sym = peek_token();
		if( sym == "" || sym == ")" || sym == "]" || sym == "}" ) {
			return ret;
		}
		auto pair = infixes.find(sym);
		int rlevel;
		if( pair == infixes.end() ) {
			if( 1000 <= level ) {
				return ret;
			}
			rlevel = 1000;
		} else {
			if( pair->second.llevel < level ) {
				return ret;
			}
			ret = Term(pair->first)(ret);
			ignore_token();
			rlevel = pair->second.rlevel;
		}
		auto r = gets_term(rlevel);
		if( r.has_value() ) {
			ret = ret(r.value());
		} else {
			return ret;
		}
	}
}

Term Syntax::get_term(int level) {
	auto const& opt = gets_term(level);
	if( !opt.has_value() ) {
		throw Error("Required a term");
	}
	return *opt;
}

