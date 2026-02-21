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
	Opt<Term> gets_term( int level = 0 ) & {
		std::string fv = "#v";
		return _gets_term(level,fv);
	}
	Term get_term( int level = 0 ) & {
		std::string fv = "#v";
		return _get_term(level,fv);
	}
	Opt<std::string> gets_sym() &;
	std::string get_sym() &;
	size_t prev_token_line = 0;
	size_t prev_token_col = 0;
private:
	Opt<Term> _gets_term( int level, std::string& fv ) &;
	Term _get_follow( Term ret, int level, Syntax const& syn, std::string& fv ) &;
	Term _get_term( int level, std::string& fv ) & {
		if( auto const& opt = _gets_term(level,fv) ) {
			return *opt;
		}
		throw Error("\"expected a term\"")(get());
	}
	Term _nest_abs( Term const& bind, int level, std::string& fv ) &;
};

#endif