#include<cctype>
#include<cstring>
#include"lexer.hpp"

using namespace std;

static int issingleop( int c ) {
	return strchr( ".,;()[]{}", c ) != NULL;
}
static int ismultiop( int c ) {
	return strchr( ":<>!@#%^&*-+=|/?", c ) != NULL;
}
static int char_done_utf8( char const* start, unsigned short count ) {
	if( !( start[count] & 0x80 ) ) {
		return true;
	}
	switch(count) {
	case 0: return ( *start & 0x80 ) == 0x00;
	case 1: return ( *start & 0xE0 ) == 0xC0;
	case 2: return ( *start & 0xF0 ) == 0xE0;
	case 3: return ( *start & 0xF8 ) == 0xF0;
	case 4: return ( *start & 0xFC ) == 0xF8;
	case 5: return ( *start & 0xFE ) == 0xFE;
	case 6: return ( *start & 0xFF ) == 0xFE;
	default:
		assert(false);
	}
}
static int char_done_sjis( char const* start, unsigned short count ) {
	return *start & 0x80 ? count >= 1 : true;
}
static int char_done_euc( char const* start, unsigned short count ) {
	return *start & 0x80 ? count >= 1 : true;
}
static int iswordchar_common( int c ) {
	return isalnum(c) || c == '_' || ( c & 0x80 );
}
Lexer::Lexer( istream& is, Encoding enc ) :
pis(&is), wp(0) {
	switch(enc) {
	case SJIS:
		char_done = char_done_sjis;
		iswordchar = iswordchar_common;
		break;
	case EUC:
		char_done = char_done_euc;
		iswordchar = iswordchar_common;
		break;
	case UTF8:
		char_done = char_done_utf8;
		iswordchar = iswordchar_common;
		break;
	}
	
}

char Lexer::read_char() {
	if( wp >= sizeof buf - 1 ) {
		strcpy( buf+20, "..." );
		cerr << "Too long token '" << buf << "'!" << endl;
		exit(-1);
	}
	char* start = &buf[wp];
	*start = pis->get();
	wp++;
	int count = 0;
	while( !char_done( start, count ) ) {
		buf[wp] = pis->get();
		wp++;
		count++;
	}
	return *start;
}
void Lexer::skip_spaces() {
	if( wp == 0 ) {
		char c;
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
}
const char* Lexer::peek_token() {
	if( wp == 0 ) {
		skip_spaces();
		if( pis->eof() ) {
			token_type = Special;
			return "";
		}
		char c = read_char();
		if( isdigit(c) ) {
			read_continue(isdigit);
			if( pis->peek() == '.' ) {
				read_char();
				read_continue(isdigit);
			}
			if( iswordchar( pis->peek() ) ) {
				read_continue(iswordchar);
				token_type = Word;
			} else {
				token_type = Number;
			}
		} else if( iswordchar(c) ) {
			read_continue(iswordchar);
			token_type = Word;
		} else if( c == '-' ) {
			if( isdigit( pis->peek() ) ) {
				read_continue(isdigit);
				token_type = Number;
			} else {
				token_type = Operator; // minus operator
			}
		} else if( c == '.' ) {
			if( isdigit( pis->peek() ) ) {
				read_continue(isdigit);
				token_type = Number;
			} else {
				token_type = Operator; // dot operator
			}
		} else if( ismultiop(c) ) {
			token_type = Operator;
			read_continue(ismultiop);
		} else if( issingleop(c) ) {
			token_type = Operator;
		} else if( c == '$' ) {
			read_continue(iswordchar);
			token_type = Escaped;
		} else {
			token_type = Special;
		}
		buf[wp] = '\0';
		return buf;
	} else {
		return buf;
	}
}
bool Lexer::readable() {
	if( wp == 0 ) {
		skip_spaces();
		return !pis->eof();
	} else {
		return true;
	}
}
bool Lexer::skips( char c ) {
	peek_token();
	if( buf[0] == c && buf[1] == '\0' ) {
		ignore_token();
		return true;
	} else {
		return false;
	}
}
bool Lexer::skips( char const* token ) {
	peek_token();
	if( strncmp( buf, token, sizeof buf ) == 0 ) {
		ignore_token();
		return true;
	} else {
		return false;
	}
}
void Lexer::skip( char const* token ) {
	if( !skips(token) ) {
		cerr << "Expected \"" << token << '"' << endl;
		throw SyntaxError();
	}
}
void Lexer::skip( char c ) {
	if( !skips(c) ) {
		cerr << "Expected \"" << c << '"' << endl;
		throw SyntaxError();
	}
}

int Lexer::get_int() {
	int ret = atoi(peek_token());
	ignore_token();
	return ret;
}
float Lexer::get_float() {
	float ret = atof(peek_token());
	ignore_token();
	return ret;
}
