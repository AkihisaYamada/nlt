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
	auto Root = Ref<Locale>::make();
	auto Preorder = Ref<Locale>::make(Root);
	Preorder->fix(LE);
	Preorder->assume( "refl", "x" &= le("x")("x") );
	auto& imp = Root->sublocale("imp",Preorder);
	imp.instantiate(Root->ctxt().cterm(IMP));
	imp.discharge([&]{
		auto loc = Locale(Root);
		loc.fix("P");
		loc.assume("P",p);
		return loc.thm("P").intro();
	}());
	cout << "imp.refl: " << Root->thm("imp.refl") << endl;

	cout << "\n--- True ---" << endl;
	Term TRUE = "true";
	auto True = Ref<Locale>::make(Root);
	{
		auto loc = Locale(True);
		loc.fix("thesis");
		loc.assume( "assm", "true" &= TRUE >>= thesis );
		Thm assm = loc.thm("assm");
		Thm imp_refl2 = loc.thm("imp.refl");
		True->obtain( assm.allE(imp_refl2).impE(imp_refl2).intro(), vector{"trueI"}.begin() );
	};

	cout << "locale True: " << *True << endl;

	cout << "\n--- And ---" << endl;
	auto And = Ref<Locale>::make(Root);
	And->fix(AND);
	And->assume( "andI1", "P" &= "Q" &= p >>= q >>= p & q );
	And->assume( "andE1", "P" &= "Q" &= p & q >>= p );
	And->assume( "andE2", "P" &= "Q" &= p & q >>= q );
	And->add_thm( "andI", [&]{
		auto loc = Locale(And);
		loc.fix("P");
		loc.fix("Q");
		loc.assume( "assm", "R" &= (p >>= q >>= r) >>= r );
		return ( loc.thm("assm") << loc.thm("andI1") ).intro();
	}() );
	And->add_thm( "andE", [&]{
		auto loc = Ref<Locale>::make(And);
		loc->fix("P");
		loc->fix("Q");
		loc->assume( "pq", p & q );
		auto loc2 = Ref<Locale>::make(loc);
		loc2->fix("R");
		loc2->assume( "pqr", p >>= q >>= r );
		Thm P = loc2->thm("andE1") << loc2->thm("pq");
		Thm Q = loc2->thm("andE2") << loc2->thm("pq");
		return (loc2->thm("pqr") << P << Q).intro().intro();
	}() );

	cout << "locale And: " << *And << endl;

	cout << "\n--- Iff ---" << endl;
	auto Iff = Ref<Locale>::make(Root);
	Iff->fix(IFF);
	Iff->assume( "iffI1", "P" &= "Q" &= (p >>= q) >>= (q >>= p) >>= (p <=> q) );
	Iff->assume( "iffE1", "P" &= "Q" &= (p <=> q) >>= p >>= q );
	Iff->assume( "iffE2", "P" &= "Q" &= (p <=> q) >>= q >>= p );
	Iff->add_thm( "iff_refl", Iff->thm("iffI1") << Iff->thm("imp.refl") << Iff->thm("imp.refl") );
	Thm iff_trans = [&]{
		auto loc = Ref<Locale>::make(Iff);
		loc->fix("P");
		loc->fix("Q");
		loc->fix("R");
		loc->assume( "PQ", p <=> q );
		loc->assume( "QR", q <=> r );
		loc->add_thm( "PR", [&]{
			auto loc2 = Ref<Locale>::make(loc);
			loc2->assume("P",p);
			loc2->add_thm( "Q", loc2->thm("iffE1") << loc2->thm("PQ") << loc2->thm("P") );
			return (loc2->thm("iffE1") << loc2->thm("QR") << loc2->thm("Q")).intro();
		}() );
		loc->add_thm( "RP", [&]{
			auto loc2 = Ref<Locale>::make(loc);
			loc2->assume("R",r);
			loc2->add_thm( "Q", loc2->thm("iffE2") << loc2->thm("QR") << loc2->thm("R") );
			return (loc2->thm("iffE2") << loc2->thm("PQ") << loc2->thm("Q")).intro();
		}() );
		return ( loc->thm("iffI1") << loc->thm("PR") << loc->thm("RP") ).intro();
	}();
	cout << "locale Iff: " << *Iff << endl;

	cout << "\n--- PropLogic ---" << endl;
	auto Logic = Ref<Locale>::make(Root);
	import(Logic->sublocale("",True));
	import(Logic->sublocale("",Iff));
	import(Logic->sublocale("",And));

	Logic->add_thm( "and_iff", Logic->thm("iffI1") << Logic->thm("andE") << Logic->thm("andI") );
	Logic->add_thm( "and_imp_iff", [&]{
		auto loc = Ref<Locale>::make(Logic);
		loc->fix("P");
		loc->fix("Q");
		loc->assume( "assm", (p>>=q) & (q>>=p) );
		loc->add_thm( "PQ", loc->thm("andE1") << loc->thm("assm") );
		loc->add_thm( "QP", loc->thm("andE2") << loc->thm("assm") );
		return ( loc->thm("iffI1") << loc->thm("PQ") << loc->thm("QP") ).intro();
	}() );
	cout << "locale Logic: " << *Logic << endl;

	cout << "=== end of test locale ===" << endl;
} catch( Error const& e ) {
	cerr << e.term << endl;
}

