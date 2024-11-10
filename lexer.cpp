#include<cctype>
#include<cuchar>
#include<cstring>
#include<charconv>
#include"lexer.hpp"

using namespace std;

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
		memcpy( buf+20, "...", 3 );
		cerr << "Too long token \"" << buf << "\"!" << endl;
		exit(-1);
	}
	char c = pis->get();
	if( c == char_traits<char>::eof() ) {
		fetched_char_type = Lex::End;
		return c;
	}
	if( c == '\n' ) {
		line_count++;
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
	fetched_char_type = plex->char_type(ch);
	return ch;
}
void Lexer::skip_spaces() {
	for(;;) {
		if( fetched_char_type == Lex::Blank ) {
			wp = 0;
			fetch_char();
			continue;
		}
	}
}
void Lexer::read_continue( Lex::CharType t ) {
	for(;;) {
		fetch_char();
		if( ( fetched_char_type & t ) == 0 ) {
			return;
		}
		rp = wp;// this character is considered read
	}
}

string_view Lexer::peek_token() {
	if( token_type == Unset ) {// no token is set
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
		switch( fetched_char_type ) {
		case Lex::Digit:
			read_continue( Lex::Digit | Lex::Dot );
			token_type = Number;
			break;
		case Lex::Dot:
			fetch_char();
			switch( fetched_char_type ) {
			case Lex::Digit: // dot followed by digits
				read_continue( Lex::Digit | Lex::Dot );
				token_type = Number;
				break;
			case Lex::Dot:
			case Lex::MultiOp:
				read_continue( Lex::MultiOp | Lex::Dot );
				token_type = Operator;
				break;
			case Lex::SingleOp:
				rp = wp;
				token_type = Operator;
				break;
			default:
				token_type = Operator; // dot operator
				break;
			}
			break;
		case Lex::MultiOp:
			read_continue( Lex::MultiOp | Lex::Dot );
			token_type = Operator;
			break;
		case Lex::SingleOp:
			token_type = Operator;
			fetched_char_type = Lex::Blank;
			break;
		case Lex::Control:
			token_type = Special;
			fetched_char_type = Lex::Blank;
			break;
		default:
			read_continue( Lex::Other | Lex::Digit );
			token_type = Word;
			break;
		}
		peeked_token = string_view(buf,rp);
	}
	return peeked_token;
}

int Tokenizer::get_int() {
	auto const& t = peek_token();
	int ret;
	from_chars(t.data(),t.data()+t.size(),ret);
	reset();
	return ret;
}
float Tokenizer::get_float() {
	auto const& t = peek_token();
	float ret;
	from_chars(t.data(),t.data()+t.size(),ret);
	reset();
	return ret;
}
