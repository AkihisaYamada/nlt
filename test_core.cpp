#include "misc.hpp"

using namespace std;

int main() try {
	cout << "=== core test ===" << endl;
	Term p = Term("P");
	Term q = Term("Q");
	Term r = Term("R");
	Term True("true");
	Term thesis("thesis");
	SYNTAX.infix(AND,35,36,36);
	SYNTAX.infix(IFF,0,1,1);

	assert( ("x" /= Term("x")) == ("y" /= Term("y")) );
	assert( ("x" /= Term("F")("x")) == ("y" /= Term("F")("y")) );

	{	Term s = "Q" &= p & q;
		Ctxt loc;
		Term t = s.subst("P",loc.fix("Q"));
		cout << "(" << s << ")(P := Q) = " << t << endl;
		assert(t == ("Q'" &= q & Term("Q'")));
	}

	Ctxt Root;
	Thm imp_refl = [&]{
		Ctxt loc = Root.branch();
		CTerm P = loc.fix("P");
		return loc.assume(P).intro();
	}();
	cout << "proved imp_refl: " << imp_refl << endl;
	Thm weaken = [&]{
		Ctxt loc = Root.branch();
		Thm P = loc.assume(loc.fix("P"));
		Thm Q = loc.assume(loc.fix("Q"));
		return P.intro();
	}();
	cout << "proved weaken: " << weaken << endl;
	Thm trueI = [&]{
		Ctxt loc = Root.branch();
		loc.fix("thesis");
		Thm assm = loc.assume("true" &= True >>= thesis);
		Thm imp_refl2 = imp_refl.weaken(loc);
		return Root.obtain(assm.allE(imp_refl2).impE(imp_refl2).intro()).second[0];
	}();
	cout << "obtained " << True << " where trueI: " << trueI << endl;
	cout << "context Root:\n" << Root << endl;
	cout << "\n--- And ---" << endl;
	Ctxt And;
	And.fix(AND);
	Thm andI1 = And.assume("P" &= "Q" &= p >>= q >>= p & q);
	cout << "assumed andI1: " << andI1 << endl;
	Thm andE1 = And.assume("P" &= "Q" &= p & q >>= p);
	cout << "assumed andE1: " << andE1 << endl;
	Thm andE2 = And.assume("P" &= "Q" &= p & q >>= q);
	cout << "assumed andE2: " << andE2 << endl;
	cout << "context And: " << endl << And << endl;
	Thm andI = [&]{
		Ctxt loc = And.branch();
		loc.fix("P");
		loc.fix("Q");
		Thm assm = loc.assume("R" &= (p >>= q >>= r) >>= r);
		Thm lem = andI1.weaken(loc).allE(p).allE(q);
		return assm.allE(loc.cterm(p & q)).impE(lem).intro();
	}();
	cout << "proved andI: " << andI << endl;
	Thm andE = [&]{
		Ctxt loc = And.branch();
		loc.fix("P");
		loc.fix("Q");
		Thm pq = loc.assume(p & q);
		Thm P = andE1.weaken(loc).allE(p).allE(q).impE(pq);
		Thm Q = andE2.weaken(loc).allE(p).allE(q).impE(pq);
		Ctxt loc2 = loc.branch();
		loc2.fix("R");
		Thm pqr = loc2.assume(p >>= q >>= r);
		return pqr.impE(P.weaken(loc2)).impE(Q.weaken(loc2)).intro().intro();
	}();
	cout << "proved andE: " << andE << endl;
	cout << "\n--- Iff ---" << endl;
	Ctxt Iff;
	Iff.fix("⟺");
	Thm iffI1 = Iff.assume("P" &= "Q" &= (p >>= q) >>= (q >>= p) >>= (p <=> q));
	cout << "assumed iffI1: " << iffI1 << endl;
	Thm iffE1 = Iff.assume("P" &= "Q" &= (p <=> q) >>= p >>= q);
	cout << "assumed iffE1: " << iffE1 << endl;
	Thm iffE2 = Iff.assume("P" &= "Q" &= (p <=> q) >>= q >>= p);
	cout << "assumed iffE2: " << iffE2 << endl;

	cout << "context Iff:\n" << Iff << endl;

	Thm iff_trans = [&]{
		Ctxt loc = Iff.branch();
		loc.fix("P");
		loc.fix("Q");
		loc.fix("R");
		Thm pq = loc.assume(p <=> q);
		Thm qr = loc.assume(q <=> r);
		Thm p_r = [&]{
			Ctxt loc2 = loc.branch();
			Thm P = loc2.assume(p);
			Thm Q = iffE1.weaken(loc2).allE(p).allE(q).impE(pq.weaken(loc2)).impE(P);
			return iffE1.weaken(loc2).allE(q).allE(r).impE(qr.weaken(loc2)).impE(Q).intro();
		}();
		Thm r_p = [&]{
			Ctxt loc2 = loc.branch();
			Thm R = loc2.assume(r);
			Thm Q = iffE2.weaken(loc2).allE(q).allE(r).impE(qr.weaken(loc2)).impE(R);
			return iffE2.weaken(loc2).allE(p).allE(q).impE(pq.weaken(loc2)).impE(Q).intro();
		}();
		return iffI1.weaken(loc).allE(p).allE(r).impE(p_r).impE(r_p).intro();
	}();
	cout << "proved iff_trans: " << iff_trans << endl;
	cout << "\n--- PropLogic ---" << endl;
	Ctxt Logic;
	Intp Logic_Iff = Intp::make(Iff,Logic);
	Logic_Iff.instantiate(Logic.fix(IFF));
	cout << "imported ⟺" << endl;
	Logic_Iff.discharge(Logic.assume((Term)iffI1));
	Logic_Iff.discharge(Logic.assume((Term)iffE1));
	Logic_Iff.discharge(Logic.assume((Term)iffE2));
	cout << "imported iffI1: " << Logic_Iff.subst(iffI1) << endl
		<< "  and iffE1: " << Logic_Iff.subst(iffE1) << endl
		<< "  and iffE2: " << Logic_Iff.subst(iffE2) << endl;
	Intp Logic_And = Intp::make(And,Logic);
	Logic_And.instantiate(Logic.fix(AND));
	Logic_And.discharge(Logic.assume((Term)andI1));
	Logic_And.discharge(Logic.assume((Term)andE1));
	Logic_And.discharge(Logic.assume((Term)andE2));
	cout << "imported andI1: " << Logic_And.subst(andI1) << endl
		<< "  and andE1: " << Logic_And.subst(andE1) << endl
		<< "  and andE2: " << Logic_And.subst(andE2) << endl;

	Thm and_iff = [&]{
		Ctxt loc = Logic.branch();
		loc.fix("P");
		loc.fix("Q");
		Thm I = Logic_And.subst(andI).weaken(loc).allE(p).allE(q);
		Thm E = Logic_And.subst(andE).weaken(loc).allE(p).allE(q);
		return Logic_Iff.subst(iffI1).weaken(loc).allE(p & q).allE("R" &= (p >>= q >>= r) >>= r).impE(E).impE(I).intro();
	}();
	cout << "proved and_iff: " << and_iff << endl;
	Thm and_imp_iff = [&]{
		Ctxt loc = Logic.branch();
		loc.fix("P");
		loc.fix("Q");
		Thm assm = loc.assume((p >>= q) & (q >>= p));
		Term PQ = (p >>= q);
		Thm pq = Logic_And.subst(andE1).weaken(loc).allE(p>>=q).allE(q>>=p).impE(assm);
		Thm qp = Logic_And.subst(andE2).weaken(loc).allE(p>>=q).allE(q>>=p).impE(assm);
		return Logic_Iff.subst(iffI1).weaken(loc).allE(p).allE(q).impE(pq).impE(qp).intro();
	}();
	cout << "proved and_imp_iff: " << and_imp_iff << endl;
	cout << "=== core test is done ===" << endl;
} catch( Error const& e ) {
	cerr << e.term << endl;
}