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
	Term init;
	if( skips("(") ) {
		init = get_term(-1000);
		skip(")");
	} else if( auto const& x = syn.finds_opener(peek) ) {
		ignore_token();
		auto const& [opener,op] = *x;
		if( auto const& var = gets_sym() ) {
			auto const& follow = peek_token();
			if( follow == "." ) {
				ignore_token();
				auto body = get_term();
				skip(op.closer);
				if( !op.compr ) throw Error("\"comprehension not registered\"")(string("\"")+opener+"\"");
				init = Term(*op.compr)(*var/=body);
			} else if( auto y = op.bcompr.finds(follow) ) {
				ignore_token();
				auto bcompr = y->second;
				auto range = get_term();
				skip(".");
				auto body = get_term();
				skip(op.closer);
				init = Term(bcompr)(range)(*var/=body),level;
			} else {
				auto inner = _get_follow(*var,0,syn);
				skip(op.closer);
				if( !op.singleton ) throw Error("\"singleton not registered\"")(inner);
				init = Term(*op.singleton)(inner);
			}
		} else {
			skip(op.closer);
			if( !op.empty ) throw Error("\"empty not registered\"");
			init = *op.empty;
		}
	} else if( auto x = syn.finds_prefix(peek) ) {
		auto const& [binder,op] = *x;
		if( op.llevel < level ) {
			return {};
		}
		ignore_token();
		if( auto const& r = gets_term(x->second.rlevel) ) {
			init = Term(binder)(*r);
		} else {
			init = binder;
		}
	} else if( auto x = syn.finds_binder(peek) ) {
		auto const& [binder,op] = *x;
		if( op.llevel < level ) {
			return {};
		}
		ignore_token();
		if( auto var = gets_sym() ) {
			auto follow = get();
			if( follow == "." ) {// ∀x. _
				auto body = get_term(op.rlevel);
				init = Term(binder)(*var/=body);
			} else if( auto y = op.bbinds.finds(follow) ) {// ∀x ∈ X. _
				auto actual = y->second;
				auto range = get_term();
				skip(".");
				auto body = get_term(op.rlevel);
				init = Term(actual)(range)(*var/=body);
			} else {
				auto inner = nest_abs(binder,op.rlevel);
				init = Term(binder)( *var /= Term(binder)(follow/=inner) );
			}
		} else {
			init = binder;
		}
	} else if( auto x = syn.finds_infix(peek) ) {
		if( x->second.level < level ) {
			return {};
		}
		init = Term(x->first);
		ignore_token();
	} else {
		auto sym = string(peek);
		ignore_token();
		if( level < 0 && skips(".") ) {
			auto body = gets_term(level);
			if( !body ) throw Error("\"binding expects body\"");
			init = sym /= *body;
		} else if( skips(".[") ) {
			auto const& body = gets_term(-1000);
			if( !body ) throw Error("\"unbinding expects body\"");
			skip("]");
			init = sym %= *body;
		} else {
			init = sym;
		}
	}
	return {_get_follow(init,level,syn)};
}
Term Parser::_get_follow( Term ret, int level, Syntax const& syn ) & {
	int lastlevel = INT_MAX;
	for(;;) {
		string_view peek = peek_token();
		if( peek == "" || syn.has_closer(peek) ) {
			return ret;
		}
		if( auto x = syn.finds_infix(peek) ) {
			auto [sym,op] = *x;
			if( op.level < level ) return ret;
			if( lastlevel < op.llevel ) return ret;
			ret = Term(sym)(ret);
			ignore_token();
			auto const& r = gets_term(op.rlevel);
			if( !r ) return ret;
			lastlevel = op.level;
			ret = ret(*r);
		} else {
			if( 1000 <= level ) return ret;
			auto const& r = gets_term(1000);
			if( !r ) return ret;
			ret = ret(*r);
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