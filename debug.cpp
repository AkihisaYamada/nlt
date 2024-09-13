#include"debug.hpp"

using namespace std;

Syntax SYNTAX;

std::ostream& operator<<(std::ostream& os, Ctxt const& c) {
	for( auto mod : c.modifiers() ) {
		if( auto fix = mod.ref<Ctxt::Fix>() ) {
			os << "\tfixes " << *fix << ';' << std::endl;
		} else if( auto assume = mod.ref<Ctxt::Assume>() ) {
			os << "\tassumes " << *assume << ';'<< std::endl;
		} else if( auto obtain = mod.ref<Ctxt::Obtain>() ) {
			os << "\tobtains " << obtain->name() << "\n\t where ";
			auto& props = obtain->props();
			out_sep(os,props.begin(),props.end(),"\n\t  and ");
			os << ';' << std::endl;
		} else {
			assert(false);
		}
	}
	return os;
}

static ostream& out_subst(ostream& os, std::pair<std::string const,Term> const& p) {
	return os << p.first << " := " << p.second;
}

ostream& operator<<(ostream& os, CSubst const& subst) {
	os << "[ ";
	auto& map = subst.map();
	out_sep(os, map.begin(), map.end(), ",\n  ", out_subst);
	return os << "\n]";
}
