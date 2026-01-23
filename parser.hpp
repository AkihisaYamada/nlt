#ifndef _PARSER_HPP_
#define _PARSER_HPP_

#include "syntax.hpp"
#include "lexer.hpp"

class Parser : public Lexer {
public:
	using Lexer::Lexer;
	virtual Syntax const& syntax() const = 0;
	Opt<std::string> gets_thm_name() &;
	std::string get_thm_name() &;
	Opt<Term> gets_term( int level = 0 ) &;
	Term get_term( int level = 0 ) &;
	Opt<std::string> gets_sym() &;
	std::string get_sym() &;
	Term nest_abs( Term const& bind, int level ) &;
	size_t prev_token_line = 0;
	size_t prev_token_col = 0;
private:
	Term _get_follow( Term ret, int level, Syntax const& syn ) &;
};

#endif