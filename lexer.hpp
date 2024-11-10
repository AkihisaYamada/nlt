#ifndef LEXER_HPP_
#define LEXER_HPP_
#include<iostream>
#include<string>
#include<cstdlib>
#include<cassert>
#include<exception>
#include<map>
#include<functional>
#include"ref.hpp"

class SyntaxError : public std::exception {};

// returns the size of the character
int char_size( char start );

int int_of_chars( char const* start );

/**
 * @brief Lexical grammar
 */
class Lex {
public:
	enum CharType {
		Blank = 1 << 0,// space or nothing
		Control = 1 << 1,
		Dot = 1 << 2,// .
		Digit = 1 << 3,
		SingleOp = 1 << 4,
		MultiOp = 1 << 5,
		Other = 1 << 6,
		End = 1 << 7,
	};
private:
	std::map<int,CharType> _char_map;
public:
	Lex();
	Lex( Lex const& other ) : _char_map(other._char_map) {}
	void register_single_op( int c ) {
		_char_map.insert({c,SingleOp});
	}
	void register_multi_op( int c ) {
		_char_map.insert({c,MultiOp});
	}
	CharType char_type( int c ) const {
		if( auto it = _char_map.find(c); it != _char_map.end() ) {
			return it->second;
		}
		return Other;
	}
	friend CharType operator|( CharType a, CharType b ) {
		return (CharType)((int)a|(int)b);
	}
};

class Tokenizer {
public:
	enum TokenType {
		Unset, Special, Word, Number, Operator, Escaped
	};
	/** reset peeked token */
	virtual void reset() = 0;
	/** peeks (not process) the next token */
	virtual std::string_view peek_token() = 0;
	std::string get_token() {
		auto ret = std::string(peek_token());
		reset();
		return ret;
	}
	/** checks if the next token is as specified, and if so, skips it */
	bool skips( std::string_view token ) {
		if( peek_token() == token ) {
			reset();
			return true;
		} else {
			return false;
		}
	}
	void skip( std::string_view token ) {
		if( !skips(token) ) {
			throw SyntaxError();
		}
	}
	template<typename T, typename... U>
	T cases(
		std::map<std::string,std::function<T(U...)>,std::less<>> map,
		std::function<T(std::string_view)> def,
		U... args
	) {
		auto token = peek_token();
		auto const& it = map.find(token);
		if( it != map.end() ) {
			reset();// skip the token
			return it->second(args...);
		} else {
			return def(token);
		}
	}
	void ignore_token() {
		peek_token();
		reset();
	}
	int get_int();
	float get_float();
	virtual std::string location() const = 0;
};

class Lexer : public Tokenizer {
private:
	/** file name */
	std::string const filename;
	/** line counter */
	size_t line_count = 1;
	// input stream
	std::istream* pis;
	/** Lexical grammar */
	Lex const* plex;
	// stores the next token type
	TokenType token_type;
	std::string_view peeked_token;
	// local buffer
	char buf[1024];
	Lex::CharType fetched_char_type;
	// write pointer
	size_t wp;
	// read pointer
	size_t rp;
	// writes one character into the buffer
	int fetch_char();
	void read_continue( Lex::CharType t );
	void skip_spaces();
	// to ensure pointer life
	Lexer( std::istream&, std::string_view const&, Lex&& ) = delete;
	// do not copy a lexer, since the internal state and the input stream get inconsistent.
	Lexer( Lexer const& ) = delete;
public:
	Lexer( std::istream& is, std::string_view const& filename, Lex const& lex ) : plex(&lex), pis(&is), filename(filename), wp(0), rp(0), token_type(Unset), fetched_char_type(Lex::Blank), buf() {}
	void reset() {
		token_type = Unset;
	}
	/** references the istream */
	std::istream& get_istream() const {
		return *pis;
	}
	/** references the lexical grammar */
	Lex const& get_lex() const {
		return *plex;
	}
	/** peeks (not process) the next token */
	std::string_view peek_token();
	TokenType next_token_type() {
		peek_token();
		return token_type;
	}
	std::string location() const {
		return filename + '+' + std::to_string(line_count);
	}
};

#endif
