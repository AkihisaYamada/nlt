#include "syntax.hpp"

using namespace std;

Syntax::Syntax() : Lex() {
	register_single_op('(');
	register_single_op(')');
	register_single_op('[');
	register_single_op(']');
	register_single_op('{');
	register_single_op('}');
	_closers.insert("]");
	register_multi_op(int_of_chars("∀"));
	register_multi_op(int_of_chars("⟹"));
	infix("⟹",2,1,1);
	prefix("∀",0,0);
}

static Syntax ROOT;

ostream& operator<<(ostream& os, Term const& t) {
	return os << ROOT.pretty_term(t,0);
}

function<ostream&(ostream&)> Syntax::pretty_term(Term const& term, int level) const {
	return [&](ostream& os) -> ostream& {
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
		for( auto const& sym : ctxt.fvar_list() ) {
			os << "  sym " << sym << endl;
		}
		os << "}" << endl;
		return os;
	};
}

Opt<string> Parser::gets_thm_name() {
	switch( next_token_type() ) {
		case Lexer::Word: break;
		case Lexer::Number: return get_token();
		default: return {};
	}
	string ret = get_token();
	for(;;) {
		if( !skips(".") ) {
			return ret;
		}
		ret += '.';
		if( next_token_type() != Lexer::Word ) {
			return ret;
		}
		ret += get_token();
	}
}
string Parser::get_thm_name() {
	if( auto const& opt = gets_thm_name() ) {
		return *opt;
	} else {
		throw Error("Required a theorem name");
	}
}

Opt<Term> Parser::gets_term(int level) {
	string_view peek = peek_token();
	if( peek == "" || _closers.contains(peek) ) {
		return {};
	}
	Term ret;
	if( auto opener_p = _openers.finds(peek) ) {
		ignore_token();
		auto const& opener = opener_p->second;
		ret = opener.handler(*this);
	} else if( auto prefix_it = _prefixes.find(peek); prefix_it != _prefixes.end() ) {
		if( prefix_it->second.llevel < level ) {
			return {};
		}
		ret = Term(prefix_it->first);
		ignore_token();
		if( auto const& r = gets_term(prefix_it->second.rlevel) ) {
			ret = ret(*r);
		}
	} else {
		string sym(peek);
		ignore_token();
		if( skips(".") ) {
			if( auto const& t = gets_term(level) ) {
				ret = sym /= *t;
			}
		} else if( skips("[") ) {
			ret = sym / *gets_term(-1000);
			skip("]");
		} else {
			ret = Term(sym);
		}
	}
	for(;;) {
		string_view peek = peek_token();
		if( peek == "" || _closers.contains(peek) ) {
			return ret;
		}
		int rlevel;
		if( auto it = _infixes.find(peek); it != _infixes.end() ) {
			if( it->second.llevel < level ) {
				return ret;
			}
			ret = Term(it->first)(ret);
			ignore_token();
			rlevel = it->second.rlevel;
		} else {
			if( 1000 <= level ) {
				return ret;
			}
			rlevel = 1000;
		}
		if( auto const& r = gets_term(rlevel) ) {
			ret = ret(*r);
		} else {
			return ret;
		}
	}
}

Term Parser::get_term(int level) {
	if( auto const& opt = gets_term(level) ) {
		return *opt;
	}
	throw Error("Required a term");
}

