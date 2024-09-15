#include<iostream>
#include "../syntax.hpp"

inline Term operator&(Term const& s, Term const& t) {
	return Term("∧")(s)(t);
}

inline Term operator<=>(Term const& s, Term const& t) {
	return Term("⟺")(s)(t);
}

/** for all */
inline Term operator&=(std::string const& v, Term const& s) {
	return ALL(v/=s);
}
