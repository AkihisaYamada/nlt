#include<iostream>
#include "util.hpp"

inline std::string const AND = "∧";
inline std::string const IFF = "⟺";

inline Term operator&(Term const& s, Term const& t) {
	return Term(AND)(s)(t);
}

inline Term operator<=>(Term const& s, Term const& t) {
	return Term(IFF)(s)(t);
}
