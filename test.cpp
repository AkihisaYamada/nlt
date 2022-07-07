#include "theories.hpp"

using namespace std;

int main() {
	Term t = Term("f")("x" %= Term("x"));
	cout << t << endl << t.fsyms() << endl;
	Theories thys;
	return 0;
}

