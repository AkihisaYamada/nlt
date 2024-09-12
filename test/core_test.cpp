#include<iostream>
#include "../core.hpp"
#include "../syntax.hpp"

using namespace std;

Term operator&(Term const& s, Term const& t) {
	return Term("∧")(s)(t);
}

/** for all */
Term operator&=(string const& v, Term const& s) {
	return ALL(v/=s);
}

int main() {
	cerr << "=== core test ===" << endl;
	Ctxt propLogic;
	propLogic.fix("∧");
	Term P = Term("P");
	Term Q = Term("Q");
	Term R = Term("R");
	Thm allE1 = propLogic.assume("P" &= "Q" &= P & Q >>= P);
	cerr << "assumed allE1: " << allE1 << endl;
	Thm allE2 = propLogic.assume("P" &= "Q" &= P & Q >>= Q);
	cerr << "assumed allE2: " << allE2 << endl;
	Thm allI1 = propLogic.assume("P" &= "Q" &= P >>= Q >>= P & Q);
	cerr << "assumed allI1: " << allI1 << endl;
	Ctxt loc = propLogic.branch();
	loc.fix("P");
	loc.fix("Q");
	Thm assm = loc.assume("R" &= (P >>= Q >>= R) >>= R);
	Thm lem = allI1.weaken(loc).allE(P).allE(Q);
	Thm allI = assm.allE(loc.cterm(P & Q)).impE(lem).intro();
	cerr << "proved allI: " << allI << endl;
}