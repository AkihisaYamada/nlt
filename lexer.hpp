#ifndef LEXER_HPP_
#define LEXER_HPP_
#include<iostream>
#include<string>
#include<cstdlib>
#include<cassert>
#include<exception>
#include<map>
#include<functional>

class SyntaxError : std::exception {};

// returns the size of the character
int char_size( char start );

int int_of_chars( char const* start );

class Lexer {
public:
	enum CharType {
		Blank = 1 << 0,// space or nothing
		Control = 1 << 1,
		Dot = 1 << 2,// .
		Digit = 1 << 3,
		SingleOp = 1 << 4,
		MultiOp = 1 << 5,
		Other = 1 << 6
	};
	enum TokenType {
		Unset, Special, Word, Number, Operator, Escaped
	};
private:
	// input stream
	std::istream* pis;
	std::map<int,CharType> char_map;
	// stores the next token type
	TokenType token_type;
	std::string_view peeked_token;
	// local buffer
	char buf[1024];
	CharType fetched_char_type;
	// write pointer
	size_t wp;
	// read pointer
	size_t rp;
	// writes one character into the buffer
	int fetch_char();
	void read_continue( CharType t );
	void skip_spaces();
public:
	Lexer( std::istream& is );
	void register_single_op( int c ) {
		char_map.insert({c,SingleOp});
	}
	void register_multi_op( int c ) {
		char_map.insert({c,MultiOp});
	}
	CharType char_type( int c ) const {
		if( auto it = char_map.find(c); it != char_map.end() ) {
			return it->second;
		}
		return Other;
	}
	// peeks (not process) the next token
	std::string_view peek_token();
	TokenType next_token_type() {
		peek_token();
		return token_type;
	}
	// checks if the next token is as specified, and if so, skips it
	bool skips( std::string_view token ) {
		if( peek_token() == token ) {
			token_type = Unset;
			return true;
		} else {
			return false;
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
			token_type = Unset;// skip the token
			return it->second(args...);
		} else {
			return def(token);
		}
	}
	void skip( std::string_view token );
	void ignore_token() {
		peek_token();
		token_type = Unset;
	}
	// process the next token
	int get_int();
	float get_float();
	std::string get_token() {
		auto ret = std::string(peek_token());
		token_type = Unset;
		return ret;
	}
	friend CharType operator|( CharType a, CharType b );
};

inline Lexer::CharType operator|( Lexer::CharType a, Lexer::CharType b ) {
	return (Lexer::CharType)((int)a|(int)b);
}

#endif
