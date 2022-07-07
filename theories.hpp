#ifndef _theories_hpp_
#define _theories_hpp_

#include"core.hpp"

struct Theories {
	Ctxt root, equational, conjunctive;
	Theories();
};

extern Term const EQ, AND;

inline Term operator^(Term const& l, Term const& r) {
	return EQ(l)(r);
}
inline Term operator&&(Term const& l, Term const& r) {
	return AND(l)(r);
}

#endif
