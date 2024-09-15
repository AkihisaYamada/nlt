#include<iostream>
#include "../util.hpp"

inline Term operator&(Term const& s, Term const& t) {
	return Term("∧")(s)(t);
}

inline Term operator<=>(Term const& s, Term const& t) {
	return Term("⟺")(s)(t);
}
