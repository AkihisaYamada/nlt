#include "misc.hpp"

using namespace std;

int main() try {
	cout << "=== core test ===" << endl;
	Term p = Term("P");
	Term q = Term("Q");
	Term r = Term("R");
	Term x = Term("x");
	Term y = Term("y");
	Term f = Term("f");
	Term True("true");
	Term thesis("thesis");
	SYNTAX.infix(AND,35,36,36);
	SYNTAX.infix(IFF,0,1,1);

	assert( ("x" /= x) == ("y" /= y) );
	assert( ("x" /= f(x)) == ("y" /= f(y)) );

	{	Term xyx = "x" &= y & x;
		Ctxt loc;
		Term t = xyx.subst("y",loc.fix("x"));
		cout << "(" << xyx << ")(y := x) = " << t << endl;
		assert(t == ("x'" &= x & Term("x'")));
	}
	{
		Ctxt loc;
		loc.fix("A");
		auto u = loc.cterm( "x" &= "A" %= x );
		auto v = loc.cterm( "y" /= "x" &= y );
		Term uv = u.Term::subst("A",v);
		cout << "(" << u << ")(A := " << v << ") = " << uv << endl;
		assert( uv == ("y" &= "x" &= y) );
		v = loc.cterm( "x'" /= "x" &= x >>= "x'" );
		uv = u.Term::subst("A",v);
		cout << "(" << u << ")(A := " << v << ") = " << uv << endl;
		assert( uv == ( "x" &= "y" &= Term("y") >>= Term("x") ) );
		loc.fix("x");
		auto w = loc.cterm( "y" /= x(y) );
		auto uw = u.Term::subst("A",w);
		cout << "(" << u << ")(A := " << w << ") = " << uw << endl;
		assert( uw == ( "y" &= x(y) ) );
		auto xyAy = loc.cterm( "x" /= "y" /= "A" %= y );
		auto yx = loc.cterm( "y" /= x );
		auto r = xyAy.Term::subst("A",yx);
		cout << "(" << xyAy << ")(A := " << yx << ") = " << r << endl;
	}

	Ctxt Root;
	Thm imp_refl = [&]{
		Ctxt loc = Root.fork().ctxt();
		CTerm P = loc.fix("P");
		return loc.assume(P).intro();
	}();
	cout << "proved imp_refl: " << imp_refl << endl;
	Thm weaken = [&]{
		Ctxt loc = Root.fork().ctxt();
		Thm P = loc.assume(loc.fix("P"));
		Thm Q = loc.assume(loc.fix("Q"));
		return P.intro();
	}();
	cout << "proved weaken: " << weaken << endl;
	Thm trueI = [&]{
		Intp child = Root.fork();
		Ctxt loc = child.ctxt();
		loc.fix("thesis");
		Thm assm = loc.assume("true" &= True >>= thesis);
		Thm imp_refl2 = imp_refl.subst(child);
		return Root.obtain("true",assm.instantiate(imp_refl2).discharge(imp_refl2).intro()).second;
	}();
	cout << "obtained " << True << " where trueI: " << trueI << endl;
	cout << "context Root:\n" << Root << endl;
	cout << "\n--- And ---" << endl;
	Intp toAnd = Root.fork();
	Ctxt And = toAnd.ctxt();
	And.fix(AND);
	Thm andI1 = And.assume("P" &= "Q" &= p >>= q >>= p & q);
	cout << "assumed andI1: " << andI1 << endl;
	Thm andE1 = And.assume("P" &= "Q" &= p & q >>= p);
	cout << "assumed andE1: " << andE1 << endl;
	Thm andE2 = And.assume("P" &= "Q" &= p & q >>= q);
	cout << "assumed andE2: " << andE2 << endl;
	cout << "context And: " << endl << And << endl;
	Thm andI = [&]{
		Intp toLoc = And.fork();
		Ctxt Loc = toLoc.ctxt();
		Loc.fix("P");
		Loc.fix("Q");
		Thm assm = Loc.assume("R" &= (p >>= q >>= r) >>= r);
		Thm lem = andI1.subst(toLoc).instantiate(p).instantiate(q);
		return assm.instantiate(Loc.cterm(p & q)).discharge(lem).intro();
	}();
	cout << "proved andI: " << andI << endl;
	Thm andE = [&]{
		Intp toLoc = And.fork();
		Ctxt Loc = toLoc.ctxt();
		Loc.fix("P");
		Loc.fix("Q");
		Thm pq = Loc.assume(p & q);
		Thm P = andE1.subst(toLoc).instantiate(p).instantiate(q).discharge(pq);
		Thm Q = andE2.subst(toLoc).instantiate(p).instantiate(q).discharge(pq);
		Intp toLoc2 = Loc.fork();
		Ctxt Loc2 = toLoc2.ctxt();
		Loc2.fix("R");
		Thm pqr = Loc2.assume(p >>= q >>= r);
		return pqr.discharge(P.subst(toLoc2)).discharge(Q.subst(toLoc2)).intro().intro();
	}();
	cout << "proved andE: " << andE << endl;
	cout << "\n--- Iff ---" << endl;
	Intp toIff = Root.fork();
	Ctxt Iff = toIff.ctxt();
	Iff.fix("⟺");
	Thm iffI1 = Iff.assume("P" &= "Q" &= (p >>= q) >>= (q >>= p) >>= (p <=> q));
	cout << "assumed iffI1: " << iffI1 << endl;
	Thm iffE1 = Iff.assume("P" &= "Q" &= (p <=> q) >>= p >>= q);
	cout << "assumed iffE1: " << iffE1 << endl;
	Thm iffE2 = Iff.assume("P" &= "Q" &= (p <=> q) >>= q >>= p);
	cout << "assumed iffE2: " << iffE2 << endl;

	cout << "context Iff:\n" << Iff << endl;

	Thm iff_trans = [&]{
		Intp toLoc = Iff.fork();
		Ctxt Loc = toLoc.ctxt();
		Loc.fix("P");
		Loc.fix("Q");
		Loc.fix("R");
		Thm pq = Loc.assume(p <=> q);
		Thm qr = Loc.assume(q <=> r);
		Thm p_r = [&]{
			Intp toLoc2 = Loc.fork();
			Ctxt Loc2 = toLoc2.ctxt();
			Intp Iff_to_Loc2 = toLoc.compose(toLoc2);
			Thm P = Loc2.assume(p);
			Thm Q = iffE1.subst(Iff_to_Loc2).instantiate(p).instantiate(q).discharge(pq.subst(toLoc2)).discharge(P);
			return iffE1.subst(Iff_to_Loc2).instantiate(q).instantiate(r).discharge(qr.subst(toLoc2)).discharge(Q).intro();
		}();
		Thm r_p = [&]{
			Intp toLoc2 = Loc.fork();
			Ctxt Loc2 = toLoc2.ctxt();
			Intp Iff_to_Loc2 = toLoc.compose(toLoc2);
			Thm R = Loc2.assume(r);
			Thm Q = iffE2.subst(Iff_to_Loc2).instantiate(q).instantiate(r).discharge(qr.subst(toLoc2)).discharge(R);
			return iffE2.subst(Iff_to_Loc2).instantiate(p).instantiate(q).discharge(pq.subst(toLoc2)).discharge(Q).intro();
		}();
		return iffI1.subst(toLoc).instantiate(p).instantiate(r).discharge(p_r).discharge(r_p).intro();
	}();
	cout << "proved iff_trans: " << iff_trans << endl;
	cout << "\n--- PropLogic ---" << endl;
	Intp toLogic = Root.fork();
	Ctxt Logic = toLogic.ctxt();
	Intp Logic_Iff = toLogic.interpret(Iff);
	Logic_Iff.instantiate(Logic.fix(IFF));
	cout << "imported ⟺" << endl;
	Logic_Iff.discharge(Logic.assume((Term)iffI1));
	Logic_Iff.discharge(Logic.assume((Term)iffE1));
	Logic_Iff.discharge(Logic.assume((Term)iffE2));
	cout << "imported iffI1: " << iffI1.subst(Logic_Iff) << endl
		<< "  and iffE1: " << iffE1.subst(Logic_Iff) << endl
		<< "  and iffE2: " << iffE2.subst(Logic_Iff) << endl;
	Intp Logic_And = toLogic.interpret(And);
	Logic_And.instantiate(Logic.fix(AND));
	Logic_And.discharge(Logic.assume((Term)andI1));
	Logic_And.discharge(Logic.assume((Term)andE1));
	Logic_And.discharge(Logic.assume((Term)andE2));
	cout << "imported andI1: " << andI1.subst(Logic_And) << endl
		<< "  and andE1: " << andE1.subst(Logic_And) << endl
		<< "  and andE2: " << andE2.subst(Logic_And) << endl;

	Thm and_iff = [&]{
		Intp toLoc = Logic.fork();
		Ctxt loc = toLoc.ctxt();
		loc.fix("P");
		loc.fix("Q");
		Thm I = andI.subst(Logic_And).subst(toLoc).instantiate(p).instantiate(q);
		Thm E = andE.subst(Logic_And).subst(toLoc).instantiate(p).instantiate(q);
		return iffI1.subst(Logic_Iff).subst(toLoc).instantiate(p & q).instantiate("R" &= (p >>= q >>= r) >>= r).discharge(E).discharge(I).intro();
	}();
	cout << "proved and_iff: " << and_iff << endl;
	Thm and_imp_iff = [&]{
		Intp toLoc = Logic.fork();
		Ctxt loc = toLoc.ctxt();
		loc.fix("P");
		loc.fix("Q");
		Thm assm = loc.assume((p >>= q) & (q >>= p));
		Term PQ = (p >>= q);
		Thm pq = andE1.subst(Logic_And).subst(toLoc).instantiate(p>>=q).instantiate(q>>=p).discharge(assm);
		Thm qp = andE2.subst(Logic_And).subst(toLoc).instantiate(p>>=q).instantiate(q>>=p).discharge(assm);
		return iffI1.subst(Logic_Iff).subst(toLoc).instantiate(p).instantiate(q).discharge(pq).discharge(qp).intro();
	}();
	cout << "proved and_imp_iff: " << and_imp_iff << endl;
	cout << "=== core test is done ===" << endl;
} catch( Error const& e ) {
	cerr << e << endl;
}