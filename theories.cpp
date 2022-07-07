#include"theories.hpp"

using namespace std;

Term const EQ = Term("=");
Term const AND = Term("∧");
Term const OR = Term("∨");
Term const EX = Term("∃");
Term const DEFINED = Term("defined");

static Term const x = Term("x");
static Term const y = Term("y");
static Term const z = Term("z");
static Term const f = Term("f");
static Term const g = Term("g");
static Term const P = Term("P");
static Term const Q = Term("Q");
static Term const R = Term("R");
static Term const alpha = Term("α");

Theories::Theories() :
	root(Ctxt("root")),
	equational(root.branch("equational")),
	logical(equational.branch("logical")
) {
	{	Ctxt local = root.branch().assume("p",P);
		root.claim("IMP.refl",local.thm("p").lift());
		local.assume("pq",P>>=Q);
		root.claim("mp",local.thm("pq").OF(local.thm("p")).lift());
	}
	cout << root << endl;

	equational.
		assume("EQ.refl", "x" %= x ^ x).
		assume("EQ.trans", "x" %= "y" %= "z" %= x ^ y >>= y ^ z >>= x ^ z).
		assume("EQ.sym", "x" %= "y" %= x ^ y >>= y ^ x).
		assume("EQ.cong", "f" %= "g" %= "x" %= "y" %= f ^ g >>= x ^ y >>= f(x) ^ g(y)).
		assume("EQ.prop1", "P" %= "Q" %= P ^ Q >>= P >>= Q);
	{	Ctxt local = equational.branch().
			assume("PQ", P ^ Q);
		Thm t = local.thm("EQ.sym");
		t = t.of(P);
		t = t.of(Q).OF(local.thm("PQ"));
		cout << t << endl;
		Thm t2 = local.thm("EQ.prop1").of(Q);
		cout << t2 << endl;
		t2 = t2.of(P);
		cout << t2 << endl;
		t2 = t2.OF(t);
		equational.claim("EQ.prop2",t2.lift());
	}
	cout << equational << endl;

	logical.
		assume("AND.def", "P" %= "Q" %= (P && Q) ^ ("R" %= (P >>= Q >>= R) >>= R)).
		assume("OR.def", "P" %= "Q" %= (P || Q) ^ ("R" %= (P >>= R) >>= (Q >>= R) >>= R)).
		assume("EX.def", "α" %= EX(alpha) ^ ("P" %= ("x" %= "α"/x >>= P) >>= P));
	{	Ctxt local = logical.branch().fix("P").fix("Q");
		Thm t = local.thm("EQ.prop1").of(P&&Q).of("R" %= (P >>= Q >>= R) >>= R);
		Thm t2 = local.thm("AND.def").of(P).of(Q);
		t = t.OF(t2);
		logical.claim("AND.elim", t.lift());
	}
	{	Ctxt local = logical.branch().assume("P",P).assume("Q",Q);
		{	Ctxt local2 = local.branch().fix("R").assume("PQR",P>>=Q>>=R);
			local.claim("rhs",
				local2.thm("PQR").OF(local2.thm("P")).
				OF(local2.thm("Q")).
				lift()
			);
		}
		Thm t = local.thm("EQ.prop2");
		t = t.of(P&&Q);
		t = t.of("R" %= (P >>= Q >>= R) >>= R);
		t = t.OF(local.thm("AND.def").of(P).of(Q));
		t = t.OF(local.thm("rhs"));
		logical.claim("AND.intro",t.lift());
	}
	{	Ctxt local = logical.branch().
			assume("Px", P(x));
		Thm t = local.thm("EX.def");
		cout << t << endl;
		t = t.of("x" /= P(x));
		cout << t << endl;
		Thm t2 = local.thm("EQ.prop2");
		cout << t2 << endl;
		t2 = t2.of(t.app()->fun.app()->arg);
		cout << t2 << endl;
		t2 = t2.of(t.app()->arg);
		cout << t2 << endl;
		t2 = t2.OF(t);
		cout << t2 << endl;
		{	Ctxt local2 = local.branch().
				assume("*", "z" %= P(z) >>= y);
			Thm t3 = local2.thm("*");
			t3 = t3.of(x).OF(local2.thm("Px"));
			cout << t3 << endl;
			local.claim("1",t3.lift());
		}
		t2 = t2.OF(local.thm("1"));
		cout << t2 << endl;
		logical.claim("EX.intro",t2.lift());
	}
	{	Ctxt local = logical.branch();
		local.assume("p_pq", P && (P >>= Q));
		Thm t = local.thm("AND.elim");
		t = t.of(P);
		t = t.of(P >>= Q);
		t = t.OF(local.thm("p_pq"));
		t = t.of(Q);
		t = t.OF(local.thm("mp").of(P).of(Q));
		logical.claim("mp2",t.lift());
	}
	cout << logical << endl;
}


/*
Ctxt definitional = equational.branch().
	assume("defined.defined",DEFINED(DEFINED)).
	assume("IMP.defined",DEFINED(IMP)).
	assume("ALL.defined",DEFINED(ALL)).
	assume("EQ.defined",DEFINED(EQ));
*/

