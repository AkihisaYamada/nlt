#include "misc.hpp"
#include "util.hpp"

using namespace std;

int main() try {
	cout << "=== util test ===" << endl;
	Term p = Term("P");
	Term q = Term("Q");
	Term r = Term("R");
	Term thesis("thesis");
	SYNTAX.infix(AND,35,36,36);
	SYNTAX.infix(IFF,0,1,1);

	Ctxt foo;
	foo.fix(AND);
	foo.fix("A");
	auto freeA = [](string_view const x) { return x == "A"; };
	auto xAx = foo.cterm( "x" &= "A" %= Term("x") );
	auto yxy = foo.cterm( "y" &= "x" &= Term("y") );
	auto unifier = unify(xAx, yxy, freeA);
	assert(unifier);
	cout << xAx << " unifies " << yxy << " via " << *unifier << endl;
	cout << xAx.subst(*unifier) << endl;
	assert( xAx.subst(*unifier) == yxy );

	auto xAxx = foo.cterm( "x" &= ("A" %= Term("x")) );
	auto yxyy = foo.cterm( "x'" &= ("x" &= Term("x'") >>= "x") );
	auto m = match(xAxx,yxyy,freeA);
	assert(m);
	cout << xAxx << " matches " << yxyy << " via " << *m << endl;
	cout << xAxx.subst(*m) << endl;
	assert( xAxx.subst(*m) == yxyy );

	Ctxt Root;
	Thm imp_refl = [&]{
		Ctxt loc = Root.branch();
		return loc.assume(loc.fix("P")).intro();
	}();
	cout << "proved imp_refl: " << imp_refl << endl;

	cout << "\n--- True ---" << endl;
	Term TRUE = "true";
	Ctxt True = Root.branch();
	Thm trueI = [&]{
		Ctxt loc = True.branch();
		loc.fix("thesis");
		Thm assm = loc.assume(loc.cterm("true" &= TRUE >>= thesis));
		Thm imp_refl2 = imp_refl.weaken(loc);
		return True.obtain("true",assm.allE(imp_refl2).impE(imp_refl2).intro()).second;
	}();
	cout << True;

	cout << "\n--- And ---" << endl;
	Ctxt And = Root.branch();
	And.fix(AND);
	Thm andI1 = And.assume("P" &= "Q" &= p >>= q >>= p & q);
	Thm andE1 = And.assume("P" &= "Q" &= p & q >>= p);
	Thm andE2 = And.assume("P" &= "Q" &= p & q >>= q);
	cout << "context And: " << endl << And << endl;
	Thm andI = [&]{
		Ctxt loc = And.branch();
		loc.fix("P");
		loc.fix("Q");
		Thm assm = loc.assume("R" &= (p >>= q >>= r) >>= r);
		return (assm << andI1).intro();
	}();
	cout << "proved andI: " << andI << endl;
	Thm andE = [&]{
		Ctxt loc = And.branch();
		loc.fix("P");
		loc.fix("Q");
		Thm pq = loc.assume(p & q);
		Thm P = andE1.weaken(loc) << pq;
		Thm Q = andE2.weaken(loc) << pq;
		Ctxt loc2 = loc.branch();
		loc2.fix("R");
		Thm pqr = loc2.assume(p >>= q >>= r);
		return (pqr << P << Q).intro().intro();
	}();
	cout << "proved andE: " << andE << endl;

	cout << "\n--- Iff ---" << endl;
	Ctxt Iff = Root.branch();
	Iff.fix(IFF);
	Thm iffI1 = Iff.assume("P" &= "Q" &= (p >>= q) >>= (q >>= p) >>= (p <=> q));
	Thm iffE1 = Iff.assume("P" &= "Q" &= (p <=> q) >>= p >>= q);
	Thm iffE2 = Iff.assume("P" &= "Q" &= (p <=> q) >>= q >>= p);

	Thm iff_refl = iffI1 << imp_refl.weaken(Iff) << imp_refl.weaken(Iff);
	cout << "proved iff_refl: " << iff_refl << endl;

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
			Thm Q = iffE1.weaken(loc2) << pq.weaken(loc2) << P;
			return (iffE1.weaken(loc2) << qr.weaken(loc2) << Q).intro();
		}();
		Thm r_p = [&]{
			Ctxt loc2 = loc.branch();
			Thm R = loc2.assume(r);
			Thm Q = iffE2.weaken(loc2) << qr.weaken(loc2) << R;
			return (iffE2.weaken(loc2) << pq.weaken(loc2) << Q).intro();
		}();
		return (iffI1.weaken(loc) << p_r << r_p).intro();
	}();
	cout << "proved iff_trans: " << iff_trans << endl;

	cout << "=== util test is done ===" << endl;
} catch( Error const& e ) {
	cerr << e.term << endl;
}