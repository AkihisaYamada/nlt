#include "misc.hpp"
#include "locale.hpp"

using namespace std;

string const LE = "≤";

int main() try {
	cout << "=== locale test ===" << endl;
	SYNTAX.infix(AND,35,36,36);
	SYNTAX.infix(IFF,0,1,1);
	SYNTAX.infix(LE,50,51,51);
	Term p = Term("P");
	Term q = Term("Q");
	Term r = Term("R");
	Term le = Term(LE);
	Term thesis = Term("thesis");
	Locale Root;
	Root.branch("Preorder");
	auto Preorder = *Root.find_locale("Preorder");
	Preorder.fix(LE);
	Preorder.add_assm( "refl", "x" &= le("x")("x") );
	Preorder.add_assm( "trans", "x" &= "y" &= "z" &= le("x")("y") >>= le("y")("z") >>= le("x")("z") );
	cout << "locale Preorder: " << Preorder << endl;
	auto& imp = Root.import("imp",Preorder);
	imp.instantiate(Root.cterm(IMP));
	imp.discharge([&]{
		Locale loc = Root.branch();
		loc.fix("P");
		loc.add_assm("P",p);
		return loc.thm("P").intro();
	}());
	imp.discharge([&]{
		Locale loc = Root.branch();
		loc.fix("P");
		loc.fix("Q");
		loc.fix("R");
		loc.add_assm( "PQ", p >>= q );
		loc.add_assm( "QR", q >>= r );
		Locale loc2 = loc.branch();
		loc2.add_assm("P",p);
		return ( loc2.thm("QR") << ( loc2.thm("PQ") << loc2.thm("P") ) ).intro().intro();
	}());
	cout << "imp.refl: " << Root.thm("imp.refl") << endl;
	cout << "imp.trans: " << Root.thm("imp.trans") << endl;

	cout << "\n--- True ---" << endl;
	Term TRUE = "true";
	Locale True = Root.branch();
	{
		Locale loc = True.branch();
		loc.fix("thesis");
		loc.add_assm( "assm", "true" &= TRUE >>= thesis );
		Thm assm = loc.thm("assm");
		Thm imp_refl2 = loc.thm("imp.refl");
		True.obtain( assm.allE(imp_refl2).impE(imp_refl2).intro(), vector{"trueI"}.begin() );
	};

	cout << "locale True: " << True << endl;

	cout << "\n--- And ---" << endl;
	Locale And = Root.branch();
	And.fix(AND);
	And.add_assm( "andI1", "P" &= "Q" &= p >>= q >>= p & q );
	And.add_assm( "andE1", "P" &= "Q" &= p & q >>= p );
	And.add_assm( "andE2", "P" &= "Q" &= p & q >>= q );
	And.add_thm( "andI", [&]{
		Locale loc = And.branch();
		loc.fix("P");
		loc.fix("Q");
		loc.add_assm( "assm", "R" &= (p >>= q >>= r) >>= r );
		return ( loc.thm("assm") << loc.thm("andI1") ).intro();
	}() );
	And.add_thm( "andE", [&]{
		Locale loc = And.branch();
		loc.fix("P");
		loc.fix("Q");
		loc.add_assm( "pq", p & q );
		Locale loc2 = loc.branch();
		loc2.fix("R");
		loc2.add_assm( "pqr", p >>= q >>= r );
		Thm P = loc2.thm("andE1") << loc2.thm("pq");
		Thm Q = loc2.thm("andE2") << loc2.thm("pq");
		return (loc2.thm("pqr") << P << Q).intro().intro();
	}() );

	cout << "locale And: " << And << endl;

	cout << "\n--- Iff ---" << endl;
	Locale Iff = Root.branch();
	Iff.fix(IFF);
	Iff.add_assm( "I1", "P" &= "Q" &= (p >>= q) >>= (q >>= p) >>= (p <=> q) );
	Iff.add_assm( "E1", "P" &= "Q" &= (p <=> q) >>= p >>= q );
	Iff.add_assm( "E2", "P" &= "Q" &= (p <=> q) >>= q >>= p );
	{
		auto& iff_preorder = Iff.import("",Preorder);
		iff_preorder.instantiate(Iff.cterm(IFF));
		iff_preorder.discharge(
			Iff.thm("I1") << Iff.thm("imp.refl") << Iff.thm("imp.refl")
		);
		iff_preorder.discharge( [&]{
			Locale loc = Iff.branch();
			loc.fix("P");
			loc.fix("Q");
			loc.fix("R");
			loc.add_assm( "PQ", p <=> q );
			loc.add_assm( "QR", q <=> r );
			loc.add_thm( "PR", [&]{
				auto loc2 = loc.branch();
				loc2.add_assm("P",p);
				loc2.add_thm( "Q", loc2.thm("E1") << loc2.thm("PQ") << loc2.thm("P") );
				return (loc2.thm("E1") << loc2.thm("QR") << loc2.thm("Q")).intro();
			}() );
			loc.add_thm( "RP", [&]{
				auto loc2 = loc.branch();
				loc2.add_assm("R",r);
				loc2.add_thm( "Q", loc2.thm("E2") << loc2.thm("QR") << loc2.thm("R") );
				return (loc2.thm("E2") << loc2.thm("PQ") << loc2.thm("Q")).intro();
			}() );
			return ( loc.thm("I1") << loc.thm("PR") << loc.thm("RP") ).intro();
		}() );
	}
	cout << "locale Iff: " << Iff << endl;

	cout << "\n--- PropLogic ---" << endl;
	Locale Logic = Root.branch();
	import_all(Logic.import("",True));
	import_all(Logic.import("iff",Iff));
	import_all(Logic.import("",And));

	Logic.add_thm( "and_iff", Logic.thm("iff.I1") << Logic.thm("andE") << Logic.thm("andI") );
	Logic.add_thm( "and_imp_iff", [&]{
		auto loc = Logic.branch();
		loc.fix("P");
		loc.fix("Q");
		loc.add_assm( "assm", (p>>=q) & (q>>=p) );
		loc.add_thm( "PQ", loc.thm("andE1") << loc.thm("assm") );
		loc.add_thm( "QP", loc.thm("andE2") << loc.thm("assm") );
		return ( loc.thm("iff.I1") << loc.thm("PQ") << loc.thm("QP") ).intro();
	}() );
	cout << "locale Logic: " << Logic << endl;

	cout << "=== end of test locale ===" << endl;
} catch( Error const& e ) {
	cerr << e.term << endl;
}

