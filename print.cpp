#include "core.hpp"

enum Level {
	TOP,
	APP_L,
	APP_R,
};

static ostream& _print(ostream& os, Term const&t, Level level) {
	{	auto sym = t.sym();
		if( sym != NULL ) {
			return os << *sym;
		}
	}
	{	auto app = t.app();
		if( app != NULL ) {
			bool paren = level > APP_L;
			if( paren ) {
				os << '(';
			}
			_print(_print(os, app->fun, APP_L) << ' ', app->arg, APP_R);
			if( paren ) {
				os << ')';
			}
			return os;
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
}

ostream& operator<<(ostream& os, Term const& t) {
	return _print(os,t,TOP);
};

ostream& operator<<(ostream& os, Ctxt const& ctxt) {
	os << "ctxt " << ctxt.name() << " {" << endl;
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
	if( t.ctxt().name() != "" ) {
		os << "(in " << t.ctxt().name() << ") ";
	}
	return os << (Term const)t;
}

ostream& operator<<(ostream& os, Syms const& syms) {
	for(auto sym : syms) {
		os << sym << ' ';
	}
	return os;
}
