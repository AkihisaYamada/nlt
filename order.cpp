#include"util.hpp"
using namespace std;

struct Comparator {
	unsigned int depth;
	StrMap<unsigned int> linds;
	StrMap<unsigned int> rinds;
	Comparator() : depth(0), linds(), rinds() {}
	int compare_var(string const& x, string const& y ) {
		auto lopt = linds.finds(x);
		auto ropt = rinds.finds(y);
		if( lopt ) {
			if( ropt ) {
				return lopt->second - ropt->second;// later bound variable is bigger
			}
			return 1; // bound > free
		}
		if( ropt ) {
			return -1; // free < bound
		}
		return x.compare(y);// free variables are literally compared
	}
	int compare(Term const& l, Term const& r) {
		if( auto lsym = l.sym() ) {
			if( auto rsym = r.sym() ) {
				return compare_var(*lsym,*rsym);
			}
			return -1;// sym < app, abs, fix
		} else if( auto lapp = l.app() ) {
			if( r.sym() ) {
				return 1; // app > sym
			}
			if( auto rapp = r.app() ) {
				if( auto pre = compare(lapp->first,rapp->first) ) {
					return pre;
				}
				return compare(lapp->second,rapp->second);
			}
			return -1; // app < abs, fix
		} else if( auto labs = l.abs() ) {
			if( r.fix() ) {
				return -1;// abs < fix
			}
			if( auto rabs = r.abs() ) {
				depth++;
				auto const& linfo = linds.emplace(labs->first,depth);
				unsigned int lprev;
				if( linfo.second ) {
					lprev = 0;
				} else {
					lprev = linfo.first->second;
					linfo.first->second = depth;
				}
				auto const& rinfo = rinds.emplace(rabs->first,depth);
				unsigned int rprev;
				if( rinfo.second ) {
					rprev = 0;
				} else {
					rprev = rinfo.first->second;
					rinfo.first->second = depth;
				}
				auto ret = compare(labs->second,rabs->second);
				if( lprev == 0 ) {
					linds.erase(linfo.first);
				} else {
					linfo.first->second = lprev;
				}
				if( rprev == 0 ) {
					rinds.erase(rinfo.first);
				} else {
					rinfo.first->second = rprev;
				}
				return ret;
			}
			return 1;// abs > sym, app
		} else if( auto lfix = l.fix() ) {
			if( auto rfix = r.fix() ) {
				if( auto pre = compare_var(lfix->first,rfix->first) ) {
					return pre;
				}
				return compare(lfix->second,rfix->second);
			}
			return 1; // fix > sym, app, abs
		} else {
			assert(false);
		}
		return false;
	}
};

int compare_term( Term const& l, Term const& r ) {
	return Comparator().compare(l,r);
}
bool operator<( Term const& l, Term const& r ) {
	return compare_term(l,r) < 0;
}
