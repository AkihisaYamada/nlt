#include<iostream>
#include "../core.hpp"
#include "../syntax.hpp"

using namespace std;

static Syntax SYNTAX;

ostream& operator<<(ostream& os, Term const& t) {
	return os << SYNTAX.pretty_term(t,0);
}

Term operator&(Term const& s, Term const& t) {
	return Term("∧")(s)(t);
}

Term operator<=>(Term const& s, Term const& t) {
	return Term("⟺")(s)(t);
}

/** for all */
Term operator&=(string const& v, Term const& s) {
	return ALL(v/=s);
}

int main() try {
	cout << "=== core test ===" << endl;
	Ctxt propLogic1;
	Term P = Term("P");
	Term Q = Term("Q");
	Term R = Term("R");
	Term True("true");
	Term thesis("thesis");
	SYNTAX.infix("∧",35,36,36);

	{	Term s = "Q" &= P & Q;
		Ctxt loc;
		Term t = s.subst("P",loc.fix("Q"));
		cout << "(" << s << ")(P := Q) = " << t << endl;
		assert(t == ("Q'" &= Q & Term("Q'")));
	}
	Thm imp_refl = [&]{
		Ctxt loc = propLogic1.branch();
		loc.fix("P");
		return loc.assume(P).intro();
	}();
	Thm trueI = [&]{
		Ctxt loc = propLogic1.branch();
		loc.fix("thesis");
		Thm assm = loc.assume("true" &= True >>= thesis);
		Thm imp_refl2 = imp_refl.weaken(loc);
		return propLogic1.obtain(assm.allE(imp_refl2).impE(imp_refl2).intro())[0];
	}();
	cout << "obtained " << True << " where trueI: " << trueI << endl;
	propLogic1.fix("∧");
	Thm andE1 = propLogic1.assume("P" &= "Q" &= P & Q >>= P);
	cout << "assumed andE1: " << andE1 << endl;
	Thm andE2 = propLogic1.assume("P" &= "Q" &= P & Q >>= Q);
	cout << "assumed andE2: " << andE2 << endl;
	Thm andI1 = propLogic1.assume("P" &= "Q" &= P >>= Q >>= P & Q);
	cout << "assumed andI1: " << andI1 << endl;
	Thm andI = [&]{
		Ctxt loc = propLogic1.branch();
		loc.fix("P");
		loc.fix("Q");
		Thm assm = loc.assume("R" &= (P >>= Q >>= R) >>= R);
		Thm lem = andI1.weaken(loc).allE(P).allE(Q);
		return assm.allE(loc.cterm(P & Q)).impE(lem).intro();
	}();
	cout << "proved andI: " << andI << endl;
	Thm andE = [&]{
		Ctxt loc = propLogic1.branch();
		loc.fix("P");
		loc.fix("Q");
		Thm pq = loc.assume(P & Q);
		Thm p = andE1.weaken(loc).allE(P).allE(Q).impE(pq);
		Thm q = andE2.weaken(loc).allE(P).allE(Q).impE(pq);
		Ctxt loc2 = loc.branch();
		loc2.fix("R");
		Thm pqr = loc2.assume(P >>= Q >>= R);
		return pqr.impE(p.weaken(loc2)).impE(q.weaken(loc2)).intro().intro();
	}();
	cout << "proved andE: " << andE << endl;
	SYNTAX.infix("⟺",0,1,1);
	propLogic1.fix("⟺");
	Thm iffI1 = propLogic1.assume("P" &= "Q" &= (P >>= Q) >>= (Q >>= P) >>= (P <=> Q));
	cout << "assumed iffI1: " << iffI1 << endl;
	Thm iffE1 = propLogic1.assume("P" &= "Q" &= (P <=> Q) >>= P >>= Q);
	cout << "assumed iffE1: " << iffE1 << endl;
	Thm iffE2 = propLogic1.assume("P" &= "Q" &= (P <=> Q) >>= Q >>= P);
	cout << "assumed iffE2: " << iffE2 << endl;
	Thm and_iff = [&]{
		Ctxt loc = propLogic1.branch();
		loc.fix("P");
		loc.fix("Q");
		Thm I = andI.weaken(loc).allE(P).allE(Q);
		Thm E = andE.weaken(loc).allE(P).allE(Q);
		return iffI1.weaken(loc).allE(P & Q).allE("R" &= (P >>= Q >>= R) >>= R).impE(E).impE(I).intro();
	}();
	cout << "proved and_iff: " << and_iff << endl;
	Thm and_imp_iff = [&]{
		Ctxt loc = propLogic1.branch();
		loc.fix("P");
		loc.fix("Q");
		Thm assm = loc.assume((P >>= Q) & (Q >>= P));
		Term PQ = (P >>= Q);
		Thm pq = andE1.weaken(loc).allE(P>>=Q).allE(Q>>=P).impE(assm);
		Thm qp = andE2.weaken(loc).allE(P>>=Q).allE(Q>>=P).impE(assm);
		return iffI1.weaken(loc).allE(P).allE(Q).impE(pq).impE(qp).intro();
	}();
	cout << "proved and_imp_iff: " << and_imp_iff << endl;
	Thm iff_imp_and = [&]{
		Ctxt loc = propLogic1.branch();
		loc.fix("P");
		loc.fix("Q");
		Thm assm = loc.assume(P <=> Q);
		Thm pq = iffE1.weaken(loc).allE(P).allE(Q).impE(assm);
		Thm qp = iffE2.weaken(loc).allE(P).allE(Q).impE(assm);
		return andI1.weaken(loc).allE(pq).allE(qp).impE(pq).impE(qp).intro();
	}();
	cout << "proved iff_imp_and: " << iff_imp_and << endl;
} catch( Error const& e ) {
	cerr << e.term << endl;
}