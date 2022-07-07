#include"theories.hpp"

using namespace std;

ostream& operator<<(ostream& os, Term const& t) {
	switch(t.type()) {
	case Term::SYM:
		return os << t.sym();
	case Term::APP:
		return os << '(' << t.fun() << ' ' << t.arg() << ')';
	case Term::ABS:
		return os << t.var() << ". " << t.body();
	default: assert(false);
	}
};

ostream& operator<<(ostream& os, Ctxt const& ctxt) {
	if( ctxt.name != NULL ) {
		os << "ctxt " << ctxt.name << " {" << endl;
	} else {
		os << "ctxt {" << endl;
	}
	for( auto sym : ctxt.sym_list() ) {
		os << "  sym " << sym << endl;
	}
	for( auto assm : ctxt.assms() ) {
		os << "  assm " << assm << endl;
	}
	for( auto thm : ctxt.thms() ) {
		os << "  thm " << thm.first << ": " << thm.second << endl;
	}
	os << "}" << endl;
	return os;
}

ostream& operator<<(ostream& os, Thm const& t) {
	if( t.ctxt()->name != NULL ) {
		os << "(in " << t.ctxt()->name << ") ";
	}
	return os << (Term const)t;
}

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

Theories::Theories() :
	root(Ctxt("root")),
	equational(root.branch("equational")),
	conjunctive(equational.branch("conjunctive")
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
		t2 = t2.of(P);
		cout << t2 << endl;
		t2 = t2.OF(t);
		equational.claim("EQ.prop2",t2.lift());
	}
	cout << equational << endl;

	conjunctive.
		assume("AND.def", "P" %= "Q" %= (P && Q) ^ ("R" %= (P >>= Q >>= R) >>= R)).
		assume("OR.def", "P" %= "Q" %= (P || Q) ^ ("R" %= (P >>= R) >>= (Q >>= R) >>= R));
	{	Ctxt local = conjunctive.branch().fix("P").fix("Q");
		Thm t = local.thm("EQ.prop1").of(P&&Q).of("R" %= (P >>= Q >>= R) >>= R);
		Thm t2 = local.thm("AND.def").of(P).of(Q);
		t = t.OF(t2);
		cout << t << endl;
		conjunctive.claim("AND.elim", t.lift());
	}
	{	Ctxt local = conjunctive.branch().assume("P",P).assume("Q",Q);
		{	Ctxt local2 = local.branch().fix("R").assume("PQR",P>>=Q>>=R);
			local.claim("rhs",
				local2.thm("PQR").OF(local2.thm("P")).
				OF(local2.thm("Q")).
				lift()
			);
		}
		Thm t = local.thm("EQ.prop2");
		cout << t << endl;
		t = t.of(P&&Q);
		cout << t << endl;
		t = t.of("R" %= (P >>= Q >>= R) >>= R);
		cout << t << endl;
		t = t.OF(local.thm("AND.def").of(P).of(Q));
		cout << t << endl;
		t = t.OF(local.thm("rhs"));
		cout << t << endl;
		conjunctive.claim("AND.intro",t.lift());
	}
	{	Ctxt local = conjunctive.branch();
		local.assume("p_pq", P && (P >>= Q));
		Thm t = local.thm("AND.elim");
		cout << t << endl;
		t = t.of(P);
		cout << t << endl;
		t = t.of(P >>= Q);
		cout << t << endl;
		t = t.OF(local.thm("p_pq"));
		cout << t << endl;
		t = t.of(Q);
		cout << t << endl;
		t = t.OF(local.thm("mp").of(P).of(Q));
		cout << t << endl;
		conjunctive.claim("mp2",t.lift());
		cout << conjunctive << endl;
	}
}


/*
Ctxt definitional = equational.branch().
	assume("defined.defined",DEFINED(DEFINED)).
	assume("IMP.defined",DEFINED(IMP)).
	assume("ALL.defined",DEFINED(ALL)).
	assume("EQ.defined",DEFINED(EQ));
*/

