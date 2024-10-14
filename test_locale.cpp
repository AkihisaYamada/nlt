#include "misc.hpp"
#include "locale.hpp"

using namespace std;

int main() try {
	cout << "=== locale test ===" << endl;
	SYNTAX.infix(AND,35,36,36);
	SYNTAX.infix(IFF,0,1,1);
	Term p = Term("P");
	Term q = Term("Q");
	Term r = Term("R");
	Term thesis("thesis");
	Term TRUE("true");
	Locale Root;
	Root.add_thm("imp_refl", [&]{
		Locale loc(Root);
		return loc.fix("P").assume("P",p).thm("P").intro();
	}());
	cout << Root;

} catch( Error const& e ) {
	cerr << e.term << endl;
}

