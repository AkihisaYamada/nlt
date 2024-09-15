#include "misc.hpp"
#include "../util.hpp"

using namespace std;

int main() {
	cout << "=== util test ===" << endl;
	Term p = Term("P");
	Term q = Term("Q");
	Term r = Term("R");
	Term True("true");
	Term thesis("thesis");
	SYNTAX.infix("∧",35,36,36);
	SYNTAX.infix("⟺",0,1,1);
	Ctxt Root;
	cout << "\n--- And ---" << endl;
	Ctxt And;
	And.fix("∧");
	Thm andI1 = And.assume("P" &= "Q" &= p >>= q >>= p & q);
	Thm andE1 = And.assume("P" &= "Q" &= p & q >>= p);
	Thm andE2 = And.assume("P" &= "Q" &= p & q >>= q);
	cout << "context And: " << endl << And << endl;
	Thm andI = [&]{
		Ctxt loc = And.branch();
		loc.fix("P");
		loc.fix("Q");
		Thm assm = loc.assume("R" &= (p >>= q >>= r) >>= r);
		return discharge(assm,andI1).intro();
	}();
	cout << "proved andI: " << andI << endl;
	Thm andE = [&]{
		Ctxt loc = And.branch();
		loc.fix("P");
		loc.fix("Q");
		Thm pq = loc.assume(p & q);
		Thm P = discharge(andE1.weaken(loc),pq);
		Thm Q = discharge(andE2.weaken(loc),pq);
		Ctxt loc2 = loc.branch();
		loc2.fix("R");
		Thm pqr = loc2.assume(p >>= q >>= r);
		return (pqr << P << Q).intro().intro();
	}();
	cout << "proved andE: " << andE << endl;
}