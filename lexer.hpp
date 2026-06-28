#ifndef LEXER_HPP_
#define LEXER_HPP_
#include<iostream>
#include<string>
#include<cstdlib>
#include<cassert>
#include<map>
#include<functional>
#include"core.hpp"

extern const Error SyntaxError;

// returns the size of the character
unsigned char char_size( char start );

unsigned int uint_of_chars( char const* start );

std::string to_hex( unsigned int i );

/**
 * @brief Lexical grammar
 */
class Lex {
public:
	enum CharType {
		None = 0,
		Letter = 1 << 0,
		Digit = 1 << 1,
		Blank = 1 << 2,// space or nothing
		Control = 1 << 3,
		End = 1 << 4,
		SingleOp = 1 << 5,
		MultiOp = 1 << 6,
		Dot = 1 << 7,// .
		DotBlank = 1 << 8,// special treatment of dot followed by blank
	};
private:
	struct _CharRange {
		int lower;// 
		CharType type;
	};
	Map<int,_CharRange> _char_ranges;// key is the upper bound
public:
	Lex();
	Lex( Lex const& other ) : _char_ranges(other._char_ranges) {}
	void register_range( int lower, int upper, CharType type );
	void register_char( int c, CharType type ) {
		register_range(c,c,type);
	}
	CharType char_type( int c ) const {
		auto u = _char_ranges.finds_bound(c);
		if( !u || c < u->second.lower ) {
			return None;// not covered
		}
		return u->second.type;
	}
	friend CharType operator|( CharType a, CharType b ) {
		return (CharType)((int)a|(int)b);
	}
};

class Tokenizer {
public:
	enum TokenType {
		Unset = 0,
		Special = 1 << 1,
		Word = 1 << 2,
		Number = 1 << 3,
		Operator = 1 << 4,
		Escaped = 1 << 5,
		Dots = 1 << 6,
		Unknown = 1 << 7,
	};
	friend TokenType operator|( TokenType a, TokenType b ) {
		return (TokenType)((int)a|(int)b);
	}
	friend TokenType operator~( TokenType a ) {
		return (TokenType)(~(int)a);
	}
public:
	/** reset peeked token */
	virtual void reset() = 0;
	/** peeked token type */
	virtual TokenType peeked_token_type() const = 0;
	/** peeks (not process) the next token */
	virtual std::string_view peek_token() = 0;
	Opt<std::string> gets( TokenType t ) {
		auto const& ret = peek_token();
		if( peeked_token_type() & t ) {
			reset();
			return std::string(ret);
		}
		return {};
	}
	std::string get( TokenType t = ~Unset ) {
		if( auto const& opt = gets(t) ) {
			return *opt;
		}
		throw SyntaxError("\"token expected\"");
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
	void skip( std::string_view exp ) {
		auto real = get();
		if( real != exp ) throw SyntaxError(exp)(real);
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
	Opt<bool> gets_bool() {
		if( skips("true") ) return {true};
		if( skips("false") ) return {false};
		return {};
	}
	bool get_bool() {
		auto ret = gets_bool();
		if( !ret ) throw SyntaxError("\"expected bool\"");
		return *ret;
	}
	Opt<size_t> gets_nat();
	size_t get_nat() {
		auto ret = gets_nat();
		if( !ret ) throw SyntaxError("\"expected nat\"");
		return *ret;
	}
	Opt<int> gets_int();
	int get_int() {
		auto ret = gets_int();
		if( !ret ) throw SyntaxError("\"expected int\"");
		return *ret;
	}
	float get_float();
	virtual std::string location() const = 0;
};

class Lexer : public Tokenizer {
private:
	/** file name */
	std::string const filename;
	/** line counter */
	size_t peeked_lines = 1;
	size_t peeked_column = 1;
	size_t read_line = 1;
	size_t read_column = 1;
	size_t prev_token_line = 1;
	size_t prev_token_column = 1;
	// input stream
	std::istream* pis;
	/** Lexical grammar */
	Lex const* const plex;
	std::string_view peeked_token;
	// stores the next token type
	TokenType token_type = Unset;
	// local buffer
	char buf[1024];
	Lex::CharType fetched_char_type;
	// write pointer
	size_t wp = 0;
	// read pointer
	size_t rp = 0;
	// writes one character into the buffer
	unsigned int fetch_char();
	void fetch_continue( Lex::CharType t );
public:
	Lexer( std::istream&, std::string_view const&, Lex&& ) = delete;
	Lexer( std::istream& is, std::string_view const& filename, Lex const& lex ) : plex(&lex), pis(&is), filename(filename), fetched_char_type(Lex::Blank), buf() {}
	// do not copy a lexer, since the internal state and the input stream get inconsistent.
	Lexer( Lexer const& ) = delete;
	void reset() {
		token_type = Unset;
	}
	TokenType peeked_token_type() const {
		return token_type;
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
		return filename + ':' + std::to_string(read_line) + ':' + std::to_string(read_column);
	}
private:
	bool _fetch_word_or_op();
	void _fetch_follower();
};

#endif
