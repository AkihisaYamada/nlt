#include<cctype>
#include<cuchar>
#include<cstring>
#include<charconv>
#include"lexer.hpp"

using namespace std;

const Error SyntaxError = Error("#syntax_error");

int char_size( char start ) {
	if( (start & 0x80) == 0x00 ) {
		return 1;
	}
	if( (start & 0xE0 ) == 0xC0 ) {
		return 2;
	}
	if( ( start & 0xF0 ) == 0xE0 ) {
		return 3;
	}
	if( ( start & 0xF8 ) == 0xF0 ) {
		return 4;
	}
	assert(false);
}

int int_of_chars( char const* start, int size ) {
	int ret = 0;
	memcpy(&ret,start,size);
	return ret;
}
int int_of_chars( char const* start ) {
	return int_of_chars( start, char_size(start[0]) );
}
Lex::Lex() :
	_char_map({
		{std::char_traits<char>::eof(),Control},
		{'.',Dot},
		{'0',Digit},
		{'1',Digit},
		{'2',Digit},
		{'3',Digit},
		{'4',Digit},
		{'5',Digit},
		{'6',Digit},
		{'7',Digit},
		{'8',Digit},
		{'9',Digit},
		{' ',Blank},
		{'\t',Blank},
		{'\n',Blank},
		{'\r',Blank},
		{'(',SingleOp},
		{')',SingleOp},
		{'[',SingleOp},
		{']',SingleOp},
		{'{',SingleOp},
		{'}',SingleOp},
	}) {}

int Lexer::fetch_char() {
	if( wp >= sizeof buf - 4 ) {
		memcpy( buf+20, "...", 4 );
		throw SyntaxError("\"Too long token\"")(string("\"")+buf+"\"");
		exit(-1);
	}
	char c = pis->get();
	peeked_column++;
	while( c == '-' && pis->peek() == '-' ) {// comment starts with "--"
		unsigned int n = 0;
		for(;;) {// count the number of '-'
			pis->ignore();
			peeked_column++;
			if( pis->peek() != '-' ) break;
			n++;
		}
		if( n == 0 ) {// line comment
			while( pis->get() != '\n' );
			peeked_lines++;
		} else {// block comment
			unsigned int m;
			for(;;) {
				char c = pis->get();
				if( c == pis->eof() ) {
					break;
				} else if( c == '\n' ) {
					peeked_lines++;
					peeked_column = 0;
				} else if( c == '-' ) {
					m = 0;
					while( pis->peek() == '-' ) {
						pis->ignore();
						peeked_column++;
						m++;
					}
					if( m > n ) {// enough '-'s to close the comment
						break;
					}
				}
				peeked_column++;
			}
		}
		c = pis->get();
	}
	if( c == char_traits<char>::eof() ) {
		fetched_char_type = Lex::End;
		return c;
	}
	if( c == '\n' ) {
		peeked_lines++;
		peeked_column = 0;
	}
	char* start = &buf[wp];
	int len = char_size(c);
	*start = c;
	wp++;
	int ch;
	switch( len ) {
	case 1:
		ch = c;
		break;
	case 4:
		buf[wp] = pis->get();
		wp++;
	case 3:
		buf[wp] = pis->get();
		wp++;
	case 2:
		buf[wp] = pis->get();
		wp++;
		ch = int_of_chars(start,len);
		break;
	}
	peeked_column += len;
	fetched_char_type = plex->char_type(ch);
	return ch;
}
void Lexer::fetch_continue( Lex::CharType t ) {
	for(;;) {
		rp = wp;// this character is considered read
		fetch_char();
		if( ( fetched_char_type & t ) == 0 ) {
			return;
		}
	}
}

string_view Lexer::peek_token() {
	if( token_type != Unset ) {// token is already fetched
		return peeked_token;
	}
	if( fetched_char_type == Lex::Blank ) {// nothing or only a space is prefetched
		do {
			wp = 0;// start from the top
			fetch_char();
		} while( fetched_char_type == Lex::Blank );
		rp = wp;// the first non-blank character is read
	} else {// a significant character is prefetched
		// move it to the top of buf
		size_t next_wp = 0;
		for( ;rp < wp; rp++, next_wp++ ) {
			buf[next_wp] = buf[rp];
		}
		wp = rp = next_wp;
	}
	prev_token_column = read_column;
	prev_token_line = read_line;
	read_line = peeked_lines;
	read_column = peeked_column;
	switch( fetched_char_type ) {
	case Lex::Digit:
		fetch_continue( Lex::Digit );
		while( fetched_char_type == Lex::Dot && isdigit(pis->peek()) ) {// allow dot followed by number
			fetch_continue( Lex::Digit );
		}
		token_type = Number;
		break;
	case Lex::DotBlank:// dot-blank is just dot.
		rp = wp;
		token_type = Dots;
		fetched_char_type = Lex::Blank;
		break;
	case Lex::Dot:
		fetch_char();
		switch( fetched_char_type ) {
		case Lex::Dot:// ..
			fetch_continue( Lex::Dot );
			if( _fetch_word_or_op() ) {
				_fetch_follower();
				token_type = Word;
			} else {
				token_type = Dots;
			}
			break;
		case Lex::Digit: // dot followed by digits
			fetch_continue( Lex::Digit );
			token_type = Number;
			break;
		case Lex::SingleOp:// dot followed by a single operator is another operator
			rp = wp;
			fetched_char_type = Lex::Blank;// no character is prefetched
			token_type = Operator;
			break;
		case Lex::MultiOp:
			fetch_continue( Lex::MultiOp );
			_fetch_follower();
			token_type = Operator;
			break;
		case Lex::Letter:
			fetch_continue( Lex::Digit | Lex::Letter );
			_fetch_follower();
			token_type = Word;
			break;
		default:
			token_type = Dots; // single dot
			break;
		}
		break;
	case Lex::SingleOp:
		token_type = Operator;
		fetched_char_type = Lex::Blank;
		break;
	case Lex::Control:
		token_type = Special;
		fetched_char_type = Lex::Blank;
		break;
	case Lex::MultiOp:
		fetch_continue( Lex::MultiOp );
		_fetch_follower();
		token_type = Operator;
		break;
	case Lex::Letter:
		fetch_continue( Lex::Letter | Lex::Digit );
		_fetch_follower();
		token_type = Word;
		break;
	}
	peeked_token = string_view(buf,rp);
	return peeked_token;
}
void Lexer::_fetch_follower() {
	while( fetched_char_type == Lex::Dot ) {
		auto old_wp = wp;// TODO
		fetch_char();
		if( fetched_char_type == Lex::Blank ) {// forget that blank is fetched
			fetched_char_type = Lex::DotBlank;
			wp = old_wp;
			return;
		}
		_fetch_word_or_op();
	}
}
bool Lexer::_fetch_word_or_op() {
	if( fetched_char_type == Lex::MultiOp ) {
		
		fetch_continue( Lex::MultiOp );
		return true;
	} else if( fetched_char_type & ( Lex::Letter | Lex::Digit ) ) {
		fetch_continue( Lex::Letter | Lex::Digit );
		return true;
	} else {
		return false;
	}
}

Opt<size_t> Tokenizer::gets_nat() {
	auto const& t = peek_token();
	int ret;
	auto last = t.data()+t.size();
	auto [ptr,ec] = from_chars(t.data(),last,ret);
	if( ptr != last ) return {};
	reset();
	return ret;
}
Opt<int> Tokenizer::gets_int() {
	if( skips("-") ) {
		return {-get_nat()};
	}
	if( auto n = gets_nat() ) {
		return {*n};
	}
	return {};
}
float Tokenizer::get_float() {
	auto const& t = peek_token();
	float ret;
	from_chars(t.data(),t.data()+t.size(),ret);
	reset();
	return ret;
}
