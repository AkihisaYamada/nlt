#include<iostream>
#include"core_writer.hpp"

using namespace std;

static ostream& write( ostream& os, Term const& t, bool paren = false ) {
	if( auto const& sym = t.sym() ) {
		return os << *sym;
	}
	if( auto const& fix = t.fix() ) {
		auto const& [v,b] = *fix;
		os << v << ".[";
		write(os,b);
		return os << "]";
	}
	if( paren ) {
		os << '(';
	}
	if( auto const& app = t.app() ) {
		auto const& [f,a] = *app;
		write(os,f);
		os << ' ';
		write(os,a,true);
	} else if( auto const& abs = t.abs() ) {
		auto const& [v,b] = *abs;
		os << v;
		os << ". ";
		write(os,b);
	} else {
		assert(false);
	}
	if( paren ) {
		os << ')';
	}
	return os;
}
ostream& operator<<( ostream& os, Term const& t ) {
	return write(os,t);
}
