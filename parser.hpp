#ifndef _PARSER_HPP_
#define _PARSER_HPP_

#include "syntax.hpp"
#include "lexer.hpp"

class Parser : public Tokenizer {
	Lexer* _lexer;
	Syntax const* _syntax;
	Parser(std::istream&,Syntax&&) = delete;
public:
	void reset() {
		_lexer->reset();
	}
	TokenType peeked_token_type() {
		return _lexer->peeked_token_type();
	}
	std::string_view peek_token() {
		return _lexer->peek_token();
	}
	std::string location() const {
		return _lexer->location();
	}
	static const Error Error;
	Parser( Lexer& lexer, Syntax const& syntax ) :
		_lexer(&lexer), _syntax(&syntax) {
//		assert( &lexer.get_lex() == &syntax );
	}
	Lexer const& get_lexer() const & {
		return *_lexer;
	}
	Lexer& get_lexer() & {
		return *_lexer;
	}
	void set_lexer( Lexer& lexer ) {
		assert( &lexer.get_lex() == _syntax );
		_lexer = &lexer;
	}
	Opt<std::string> gets_thm_name();
	std::string get_thm_name();
	Opt<Term> gets_term(int level = 0);
	Term get_term(int level = 0);
	Term nest_abs( Term const& bind, int level );
};

#endif