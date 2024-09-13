#ifndef _DEBUG_HPP_
#define _DEBUG_HPP_

#include<ostream>
#include"core.hpp"
#include"syntax.hpp"

#define DEB(expr) do { std::cerr << __FILE__ << ":" << __LINE__ << ": " << expr << endl; } while(0)

template<class I, class T = I::value_type>
void out_sep(
	std::ostream& os, I it, I const& end, std::string const& sep, std::ostream& elm(std::ostream&,T const&) = operator<< ) {
	if( it != end ) {
		elm(os,*it);
		it++;
		while( it != end ) {
			os << sep;
			elm(os,*it);
			it++;
		}
	}
}

extern Syntax SYNTAX;

inline std::ostream& operator<<(std::ostream& os, Term const& t) {
	return os << SYNTAX.pretty_term(t,0);
}

std::ostream& operator<<(std::ostream& os, CSubst const& subst);

std::ostream& operator<<(std::ostream& os, Ctxt const& ctxt);

#endif
