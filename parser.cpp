#include "parser.hpp"

using namespace std;

Opt<string> Parser::gets_thm_name() {
	string ret;
	switch( _lexer->next_token_type() ) {
		case Lexer::Dots:
			ret = _lexer->get_token();
			if( _lexer->next_token_type() == Lexer::Word ) {
				ret += _lexer->get_token();
			}
			break;
		case Lexer::Word:
			ret = _lexer->get_token();
			break;
		case Lexer::Number: return _lexer->get_token();
		default: return {};
	}
	for(;;) {
		if( !_lexer->skips(".") ) {
			return ret;
		}
		ret += '.';
		if( _lexer->next_token_type() != Lexer::Word ) {
			return ret;
		}
		ret += _lexer->get_token();
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
	string_view peek = _lexer->peek_token();
	if( peek == "" || _syntax->has_closer(peek) ) {
		return {};
	}
	Term ret;
	if( auto opener_p = _syntax->finds_opener(peek) ) {
		_lexer->ignore_token();
		auto const& opener = opener_p->second;
		ret = opener.handler(*this);
	} else if( auto x = _syntax->finds_prefix(peek) ) {
		if( x->second.llevel < level ) {
			return {};
		}
		ret = Term(x->first);
		_lexer->ignore_token();
		if( auto const& r = gets_term(x->second.rlevel) ) {
			ret = ret(*r);
		}
	} else if( auto x = _syntax->finds_infix(peek) ) {
		if( x->second.level < level ) {
			return {};
		}
		ret = Term(x->first);
		_lexer->ignore_token();
	} else {
		string sym(peek);
		_lexer->ignore_token();
		if( _lexer->skips(".") ) {
			if( auto const& t = gets_term(level) ) {
				ret = sym /= *t;
			}
		} else if( _lexer->skips(".[") ) {
			auto const& t = gets_term(-1000);
			if( !t ) {
				throw Error("#term");
			}
			ret = sym %= *t;
			_lexer->skip("]");
		} else {
			ret = Term(sym);
		}
	}
	for(;;) {
		string_view peek = _lexer->peek_token();
		if( peek == "" || _syntax->has_closer(peek) ) {
			return ret;
		}
		int rlevel;
		if( auto x = _syntax->finds_infix(peek) ) {
			if( x->second.llevel < level ) {
				return ret;
			}
			ret = Term(x->first)(ret);
			_lexer->ignore_token();
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

Term Parser::get_term(int level) {
	if( auto const& opt = gets_term(level) ) {
		return *opt;
	}
	throw Error("Required a term");
}

