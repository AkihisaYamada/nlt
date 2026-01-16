#include "parser.hpp"

using namespace std;

Opt<string> Parser::gets_thm_name() & {
	return gets(Lexer::Word|Lexer::Number);
}
string Parser::get_thm_name() & {
	if( auto const& opt = gets_thm_name() ) {
		return *opt;
	}
	throw Error("Required a theorem name");
}

Term Parser::nest_abs( Term const& bind, int level ) & {
	if( auto next = gets(Lexer::Word) ) {
		return bind( *next /= nest_abs(bind,level) );
	}
	skip(".");
	return get_term(level);
}
Opt<Term> Parser::gets_term( int level ) & {
	auto& syn = syntax();
	string_view peek = peek_token();
	if( peek == "" || syn.has_closer(peek) ) {
		return {};
	}
	Term ret;
	if( auto opener_p = syn.finds_opener(peek) ) {
		ignore_token();
		auto const& opener = opener_p->second;
		ret = opener.handler(*this);
	} else if( auto x = syn.finds_prefix(peek) ) {
		if( x->second.llevel < level ) {
			return {};
		}
		ret = Term(x->first);
		ignore_token();
		if( auto const& r = gets_term(x->second.rlevel) ) {
			ret = ret(*r);
		}
	} else if( auto x = syn.finds_binder(peek) ) {
		if( x->second.llevel < level ) {
			return {};
		}
		ignore_token();
		auto var = gets(Lexer::Word);
		if( !var && skips("(") ) {
			var = get();
			skip(")");
		}
		if( var ) {
			auto follow = get();
			if( follow == "." ) {
				ret = Term(x->first)( *var /= get_term(x->second.rlevel) );
			} else if( auto y = x->second.mids.finds(follow) ) {
				auto sym = y->second;
				auto typ = get_term();
				skip(".");
				auto body = get_term(x->second.rlevel);
				ret = Term(sym)(typ)(*var/=body);
			} else {
				ret = Term(x->first)( *var /= Term(x->first)( follow /= nest_abs(x->first,x->second.rlevel) ) );
			}
		} else {
			ret = Term(x->first);
		}
	} else if( auto x = syn.finds_infix(peek) ) {
		if( x->second.level < level ) {
			return {};
		}
		ret = Term(x->first);
		ignore_token();
	} else {
		auto sym = string(peek);
		ignore_token();
		if( level < 0 && skips(".") ) {
			auto t = gets_term(level);
			if( !t ) throw Error("\"binding expects body\"");
			ret = sym /= *t;
		} else if( skips(".[") ) {
			auto const& t = gets_term(-1000);
			if( !t ) throw Error("\"unbinding expects body\"");
			ret = sym %= *t;
			skip("]");
		} else {
			ret = Term(sym);
		}
	}
	for(;;) {
		string_view peek = peek_token();
		if( peek == "" || syn.has_closer(peek) ) {
			return ret;
		}
		int rlevel;
		if( auto x = syn.finds_infix(peek) ) {
			if( x->second.llevel < level ) {
				return ret;
			}
			ret = Term(x->first)(ret);
			ignore_token();
			rlevel = x->second.rlevel;
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

Term Parser::get_term( int level ) & {
	if( auto const& opt = gets_term(level) ) {
		return *opt;
	}
	throw Error("\"expected a term\"")(get());
}

Opt<string> Parser::gets_sym() & {
	auto& syn = syntax();
	string_view peek = peek_token();
	if( peek == "(" ) {
		ignore_token();
		auto ret = get();
		skip(")");
		return {ret};
	}
	if( peek == "" || syn.has_closer(peek) || syn.finds_opener(peek) || syn.finds_binder(peek) || syn.finds_prefix(peek) || syn.finds_infix(peek) ) {
		return {};
	}
	return {get()};
}
string Parser::get_sym() & {
	if( auto o = gets_sym() ) {
		return *o;
	}
	throw Error("\"expected a symbol\"")(get());
}