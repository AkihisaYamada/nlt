#include<cctype>
#include<cuchar>
#include<cstring>
#include<charconv>
#include"lexer.hpp"

using namespace std;

const Error SyntaxError = Error("#syntax_error");

unsigned char char_size( char start ) {
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

unsigned int uint_of_chars( unsigned char const* start, unsigned char size ) {
	unsigned int ret = 0;
	for( size_t i = 0; i < size; i++ ) {
		ret = (ret << 8) | (unsigned char)start[i];
	}
	return ret;
}
unsigned int uint_of_chars( char const* start ) {
	return uint_of_chars( (unsigned char*)start, char_size(start[0]) );
}
string to_hex( unsigned int i ) {
	static char const* H = "0123456789abcdef";
	if( i == 0 ) return "0";
	size_t l = sizeof(int)*8 - 4;
	unsigned char d;
	for(;;) {
		d = i>>l;
		if( d != 0 ) break;
		l -= 4;
	}
	string ret = {H[d]};
	while( l != 0 ) {
		i ^= d<<l;
		l -= 4;
		d = i>>l;
		ret.push_back(H[d]);
	};
	return ret;
}
Lex::Lex() :
	_char_ranges({
		{std::char_traits<char>::eof(),{std::char_traits<char>::eof(),Control}},
		{'.',{'.',Dot}},
		{'9',{'0',Digit}},
		{' ',{' ',Blank}},
		{'\t',{'\t',Blank}},
		{'\n',{'\n',Blank}},
		{'\r',{'\r',Blank}},
		{')',{'(',SingleOp}},
		{'[',{'[',SingleOp}},
		{']',{']',SingleOp}},
		{'{',{'{',SingleOp}},
		{'}',{'}',SingleOp}},
		{'Z',{'A',Letter}},
		{'z',{'a',Letter}},
	}) {}

void Lex::register_range( int lower, int upper, CharType type ) {
	if( upper < lower ) throw Error("\"negative range\"")(to_hex(lower))(to_hex(upper));
	if( auto l = _char_ranges.finds_bound(lower) ) {
		if( l->first <= lower || l->second.lower <= upper ) throw Error("\"char range overlapping with lower\"");
		if( auto u = _char_ranges.finds_bound(upper) ) {
			if( u->first <= upper ) throw Error("\"char range overlapping with upper\"");
		}
	}
	_char_ranges.emplace(upper,_CharRange{lower,type});
}

unsigned int Lexer::fetch_char() {
	if( wp >= sizeof buf - 4 ) {
		memcpy( buf+20, "...", 4 );
		throw SyntaxError("\"Too long token\"")(string("\"")+buf+"\"");
		exit(-1);
	}
	char c = pis->get();
	peeked_column++;
	if( c == '-' && pis->peek() == '-' ) {// comment starts with "--"
		unsigned int n = 0;
		for(;;) {// count the number of '-'
			pis->ignore();
			peeked_column++;
			if( pis->peek() != '-' ) break;
			n++;
		}
		if( n == 0 ) {// line comment
			while( pis->get() != '\n' );
			peeked_column = 0;
			peeked_lines++;
		} else {// block comment
			unsigned int m;
			for(;;) {
				char c = pis->get();
				if( c == pis->eof() ) {
					break;
				} else if( c == '\n' ) {
					peeked_column = 0;
					peeked_lines++;
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
		// read comment as a space.
		fetched_char_type = Lex::Blank;
		return ' ';
	}
	if( c == char_traits<char>::eof() ) {
		fetched_char_type = Lex::End;
		return c;
	}
	if( c == '\n' ) {
		peeked_column = 0;
		peeked_lines++;
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
		ch = uint_of_chars((unsigned char*)start,len);
		break;
	}
	peeked_column += len;
	fetched_char_type = plex->char_type(ch);
	return ch;
}
bool Lexer::_fetch_while( Lex::CharType t ) {
	if( fetched_char_type & t ) {
		_fetch_continue(t);
		return true;
	}
	return false;
}
void Lexer::_fetch_continue( Lex::CharType t ) {
	for(;;) {
		rp = wp;// this character is considered read
		fetch_char();
		if( ( fetched_char_type & t ) == 0 ) {
			return;
		}
	}
}

string_view Lexer::peek_token() {
	if( token_type != UNSET ) {// token is already fetched
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
		_fetch_continue( Lex::Digit );
		switch( fetched_char_type ) {
		case Lex::Underscore:// 123_
			fetch_char();
			if( _fetch_while( Lex::Letter | Lex::Digit ) ) {
				_fetch_follower(Lex::Letter);
			}
			token_type = WORD;
			break;			
		case Lex::Dot:// 123.456
			if( isdigit(pis->peek()) ) {
				_fetch_continue( Lex::Digit );
			}
		default:
			token_type = NUMBER;
		}
		break;
	case Lex::DotBlank:// dot-blank is just dot.
		rp = wp;
		token_type = DOTS;
		fetched_char_type = Lex::Blank;
		break;
	case Lex::Dot:
		fetch_char();
		switch( fetched_char_type ) {
		case Lex::Dot:// ..
			_fetch_continue( Lex::Dot );
			if( _fetch_while( Lex::Letter | Lex::Digit ) ) {// ..a
				_fetch_follower(Lex::Letter);
				token_type = WORD;
			} else {
				token_type = DOTS;
			}
			break;
		case Lex::Digit: // dot followed by digits
			_fetch_continue( Lex::Digit );
			token_type = NUMBER;
			break;
		case Lex::SingleOp:// dot followed by a single operator is another operator
			rp = wp;
			fetched_char_type = Lex::Blank;// no character is prefetched
			token_type = OPERATOR;
			break;
		case Lex::MultiOp:
			_fetch_continue(Lex::MultiOp);
			_fetch_follower(Lex::MultiOp);
			token_type = OPERATOR;
			break;
		case Lex::Letter:
			_fetch_continue( Lex::Digit | Lex::Letter );
			_fetch_follower(Lex::Letter);
			token_type = WORD;
			break;
		default:
			token_type = DOTS; // single dot
			break;
		}
		break;
	case Lex::SingleOp:
		rp = wp;
		fetch_char();
		_fetch_follower(Lex::SingleOp);
		token_type = OPERATOR;
		break;
	case Lex::MultiOp:
		_fetch_continue(Lex::MultiOp);
		_fetch_follower(Lex::MultiOp);
		token_type = OPERATOR;
		break;
	case Lex::Quote: {
		fetch_char();
		rp = wp;// anything following quote is read
		auto first_quote_type = fetched_char_type;
		fetch_char();
		if( fetched_char_type == Lex::Quote ) {// 'a'
			rp = wp;
			fetched_char_type = Lex::None;
			token_type = WORD;
			break;
		}
		if( first_quote_type & ( Lex::Letter | Lex::Digit ) ) {
			if( _fetch_while( Lex::Letter | Lex::Digit ) ) {
				_fetch_follower(Lex::Letter);
			}
			token_type = WORD;
			break;
		}
		throw SyntaxError("\"unsupported token\"");
	} break;
	case Lex::Letter:
		_fetch_continue( Lex::Letter | Lex::Digit );
		_fetch_follower(Lex::Letter);
		token_type = WORD;
		break;
	case Lex::Underscore:
		fetch_char();
		if( _fetch_while( Lex::Letter | Lex::Digit ) ) {
			_fetch_follower(Lex::Letter);
		} else if( _fetch_while( Lex::MultiOp ) ) {
			_fetch_follower(Lex::MultiOp);
		}
		token_type = WORD;
		break;
	default:
		token_type = SPECIAL;
		fetched_char_type = Lex::Blank;
		break;
	}
	peeked_token = string_view(buf,rp);
	return peeked_token;
}
void Lexer::_fetch_follower( Lex::CharType prevtype ) {
	for(;;) {
		switch( prevtype ) {
		case Lex::Letter: case Lex::Digit: case Lex::MultiOp: case Lex::Underscore: case Lex::Quote:
			if( _fetch_while(Lex::Underscore) ) {
				prevtype = fetched_char_type;
				_fetch_word_or_op();
				continue;
			}
			if( _fetch_while(Lex::Quote) ) {
				prevtype = fetched_char_type;
				_fetch_word_or_num();
				continue;
			}
		case Lex::SingleOp:
			if( fetched_char_type == Lex::Dot ) {
				auto old_wp = wp;// TODO
				fetch_char();
				if( fetched_char_type == Lex::Blank ) {// forget that blank is fetched
					fetched_char_type = Lex::DotBlank;
					wp = old_wp;
					return;
				}
				prevtype = fetched_char_type;
				_fetch_word_or_op();
				continue;
			}
		}
		return;
	}
}

Opt<size_t> Tokenizer::gets_nat( std::function<bool(size_t)> const& test ) {
	auto const& t = peek_token();
	int ret;
	auto last = t.data()+t.size();
	auto [ptr,ec] = from_chars(t.data(),last,ret);
	if( ptr != last ) return {};
	reset();
	if( !test(ret) ) throw Error("\"out of range\"")(to_string(ret));
	return ret;
}
Opt<int> Tokenizer::gets_int( std::function<bool(int)> const& test ) {
	int ret;
	if( skips("-") ) {
		ret = -(int)get_nat();
	} else {
		auto n = gets_nat();
		if( !n ) return {};
		ret = *n;
	}
	if( !test(ret) ) throw Error("\"out of range\"")(to_string(ret));
	return ret;
}
float Tokenizer::get_float() {
	auto const& t = peek_token();
	float ret;
	from_chars(t.data(),t.data()+t.size(),ret);
	reset();
	return ret;
}
