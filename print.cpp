#include "core.hpp"

ostream& operator<<(ostream& os, Term const& t) {
	{	auto sym = t.sym();
		if( sym != NULL ) {
			return os << *sym;
		}
	}
	{	auto app = t.app();
		if( app != NULL ) {
			return os << '(' << app->fun << ' ' << app->arg << ')';
		}
	}
	{	auto abs = t.abs();
		if( abs != NULL ) {
			return os << abs->var << ". " << abs->body;
		}
	}
	{	auto fix = t.fix();
		if( fix != NULL ) {
			return os << fix->var << "[" << fix->val << "]";
		}
	}
	assert(false);
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
