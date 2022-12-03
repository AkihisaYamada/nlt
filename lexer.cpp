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

Lexer::Lexer( istream& is ) : pis(&is), wp(0), rp(0), token_type(Unset), fetched_char_type(Blank), buf(),
	char_map({
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
	}) {}

int Lexer::fetch_char() {
	if( wp >= sizeof buf - 4 ) {
		memcpy( buf+20, "...", 3 );
		cerr << "Too long token \"" << buf << "\"!" << endl;
		exit(-1);
	}
	char c = pis->get();
	if( c == char_traits<char>::eof() ) {
		return c;
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
	fetched_char_type = char_type(ch);
	return ch;
}
void Lexer::skip_spaces() {
	unsigned char c;
	for(;;) {
		while( isspace( c = pis->peek() ) ) {
			pis->ignore();
		}
		if( c == '#' ) {
			while( ! pis->eof() && pis->get() != '\n' );
			continue;
		} else {
			break;
		}
	}
}
void Lexer::read_continue( CharType t ) {
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
		if( fetched_char_type == Blank ) {// nothing or only a space is prefetched
			skip_spaces();
			wp = 0;// start from the top
			fetch_char();
			rp = wp;// the first character is always read
		} else {// a significant character is prefetched
			// move it to the top of buf
			size_t next_wp = 0;
			for( ;rp < wp; rp++, next_wp++ ) {
				buf[next_wp] = buf[rp];
			}
			wp = rp = next_wp;
		}
		switch( fetched_char_type ) {
		case Digit:
			read_continue(Digit|Dot);
			token_type = Number;
			break;
		case Dot:
			fetch_char();
			switch( fetched_char_type ) {
			case Digit: // dot followed by digits
				read_continue(Digit|Dot);
				token_type = Number;
				break;
			case Dot:
			case MultiOp:
				read_continue(MultiOp|Dot);
				token_type = Operator;
				break;
			case SingleOp:
				rp = wp;
				token_type = Operator;
				break;
			default:
				token_type = Operator; // dot operator
				break;
			}
			break;
		case MultiOp:
			read_continue(MultiOp|Dot);
			token_type = Operator;
			break;
		case SingleOp:
			token_type = Operator;
			fetched_char_type = Blank;
			break;
		case Control:
			token_type = Special;
			fetched_char_type = Blank;
			break;
		default:
			read_continue(Other|Digit);
			token_type = Word;
			break;
		}
		peeked_token = string_view(buf,rp);
	}
	return peeked_token;
}
bool Lexer::readable() {
	if( wp == 0 ) {
		skip_spaces();
		return !pis->eof();
	} else {
		return true;
	}
}

void Lexer::skip( string_view token ) {
	if( !skips(token) ) {
		cerr << "Expected \"" << token << "\" but encountered \"" <<
			peeked_token <<'"' << endl;
		throw SyntaxError();
	}
}

int Lexer::get_int() {
	peek_token();
	int ret;
	from_chars(buf,buf+rp,ret);
	token_type = Unset;
	return ret;
}
float Lexer::get_float() {
	peek_token();
	float ret;
	from_chars(buf,buf+rp,ret);
	token_type = Unset;
	return ret;
}
