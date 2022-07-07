#ifndef _theories_hpp_
#define _theories_hpp_

#include<iostream>
#include"core.hpp"

ostream& operator<<(ostream& os, Term const& t);
ostream& operator<<(ostream& os, Ctxt const& ctxt);
ostream& operator<<(ostream& os, Thm const& t);

struct Theories {
	Ctxt root, equational, conjunctive;
	Theories();
};

extern Term const EQ, AND, OR;

inline Term operator^(Term const& l, Term const& r) {
	return EQ(l)(r);
}
inline Term operator&&(Term const& l, Term const& r) {
	return AND(l)(r);
}

inline Term operator||(Term const& l, Term const& r) {
	return OR(l)(r);
}

#endif
