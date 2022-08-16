#ifndef LEXER_HPP_
#define LEXER_HPP_
#include<iostream>
#include<string>
#include<cstdlib>
#include<cassert>
#include<exception>
#include"string.hpp"

class SyntaxError : std::exception {};

class Lexer {
public:
	enum Encoding {
		SJIS, EUC, UTF8
	};
	enum TokenType {
		Special, Word, Number, Operator, Escaped
	};
	Lexer( std::istream& is, Encoding enc = UTF8 );
private:
	// tests if a wide charactor is done in the size 'len'
	int (*char_done)( char const* start, unsigned short len );
	// tests if a charactor forms a word (typically, isalnum)
	int (*iswordchar)( int c );
	// stores the next token type
	TokenType token_type;
	// input stream
	std::istream* pis;
	// local buffer
	char buf[1024];
	// write pointer
	size_t wp;
	// reads one charactor into the buffer
	char read_char();
	// reads until f fails
	void read_continue( int (*f)(int) ) {
		while( f( pis->peek() ) ) {
			read_char();
		}
	}
public:
	void skip_spaces();
	// peeks (not process) the next token
	char const* peek_token();
	TokenType next_token_type() {
		peek_token();
		return token_type;
	}
	// ignores next token
	void ignore_token() {
		peek_token();
		wp = 0;
	}
	// if more token follows
	bool readable();
	// checks if the next charactor/token is as specified, and if so, skips it
	bool skips( char c );
	bool skips( char const* token );
	void skip( char const* token );
	void skip( char c );

	// process the next token
	int get_int();
	float get_float();
	std::string get_token() {
		std::string ret = peek_token();
		ignore_token();
		return ret;
	}
};
#endif
