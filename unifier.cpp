#include"util.hpp"

using namespace std;

class Unifier {
	std::function<bool(String const&)> const& fvar;// free variables
	CSubst subst;
public:
	struct Mismatch : exception {};
	struct Occurs : exception {};
	struct Escapes : exception {};
	Unifier(Ctxt const& ctxt, std::function<bool(String const&)> const& fvar) : subst(ctxt), fvar(fvar) {}
private:
	map<String,unsigned int,less<>> escapes[2];
	StrSet avoids[2];

	static Term sanitize(Term const& t, StrSet& bounds, StrSet const& avoids, map<String,unsigned int,less<>> const& escapes) {
		auto const& sym = t.sym();
		if( sym.has_value() ) {
			String const& x = *sym;
			if( bounds.contains(x) ) {// local bound variable is OK
				return x;
			}
			if( avoids.contains(x) ) {// occurs check
				throw Occurs();
			}
			if( escapes.contains(x) ) {// variable must not escape
				throw Escapes();
			}
			return t;
		}
		auto const& app = t.app();
		if( app.has_value() ) {
			return sanitize(app->first,bounds,avoids,escapes)(sanitize(app->second,bounds,avoids,escapes));
		}
		auto const& abs = t.abs();
		if( abs.has_value() ) {
			String const& x = abs->first;
			auto const& info = bounds.insert(x);
			auto const& body = sanitize(abs->second,bounds,avoids,escapes);
			if( info.second ) {
				bounds.erase(info.first);
			}
			return x /= body;
		}
		auto const& fix = t.fix();
		assert( fix.has_value() );
		return fix->first / sanitize(fix->second,bounds,avoids,escapes);
	}

	void unify1(String const& x, Term const& r) {
		auto const& rsym = r.sym();
		if( rsym.has_value() ) {
			String const& y = *rsym;
			if( x == y ) {
				return;
			}
			if( escapes[1].contains(y) ) { // this case is already tested
				throw Mismatch();
			}
			// test if y has an assigned value.
			auto ysubst = subst.get(y);
			if( ysubst.has_value() ) {
				unify1(x,*ysubst);
				return;
			}
			if( fvar(y) ) {// free variables can be assigned
				StrSet bounds;
				subst.assign(y,x);
				return;
			}
		}
		throw Mismatch();
	}
	void unify2(Term const& l, Term const& r, unsigned int index) {
		auto const& rsym = r.sym();
		if( rsym.has_value() ) {
			String const& y = *rsym;
			if( escapes[1].contains(y) ) { // bound variable cannot match other things
				throw Mismatch();
			}
			// test if y has an assigned value.
			auto ysubst = subst.get(y);
			if( ysubst.has_value() ) {
				avoids[0].insert(y);// this rhs cannot be unified with lhs containing y
				unify2(l,*ysubst,index);
				avoids[0].erase(y);
				return;
			}
			if( fvar(y) ) {// free variables can be assigned
				StrSet bounds;
				subst.assign(y,sanitize(l,bounds,avoids[0],escapes[0]));
				return;
			}
			throw Mismatch();
		}
		auto const& lapp = l.app();
		if( lapp.has_value() ) {
			auto const& rapp = r.app();
			if( !rapp.has_value() ) {
				throw Mismatch();
			 }
			unify(lapp->first,rapp->first,index);
			unify(lapp->second,rapp->second,index);
			return;
		}
		auto const& labs = l.abs();
		if( labs.has_value() ) {
			auto const& rabs = r.abs();
			if( !rabs.has_value() ) {
				throw Mismatch();
			}
			// both are abstraction.
			String const& x = labs->first;
			String const& y = rabs->first;
			auto const& xinfo = escapes[0].insert({x,index});
			auto const& yinfo = escapes[1].insert({y,index});
			unify(labs->second,rabs->second,index+1);
			// forget the bound variables
			if( xinfo.second ) {
				escapes[0].erase(xinfo.first);
			}
			if( yinfo.second ) {
				escapes[1].erase(yinfo.first);
			}
			return;
		}
		auto const& lfix = l.fix();
		assert( lfix.has_value() );
		auto const& rfix = r.fix();
		if( !rfix.has_value() || lfix->first != rfix->first ) {
			throw Mismatch();
		}
		unify(lfix->second,rfix->second,index);
		return;
	}
public:
	void unify(Term const& l, Term const& r, unsigned int index = 0) {
		auto const& lsym = l.sym();
		if( lsym.has_value() ) {
			String const& x = *lsym;
			auto const& xesc_it = escapes[0].find(x);
			if( xesc_it != escapes[0].end() ) {// bound variable must have the same index.
				auto const& rsym = r.sym();
				if( rsym.has_value() ) {
					auto const& yesc_it = escapes[1].find(*rsym);
					if( yesc_it != escapes[1].end() ) {
						if( xesc_it->second == yesc_it->second ) {
							return;
						}
					}
				}
				throw Mismatch();
			}
			if( x == r ) {
				return;
			}
			// test if substitution is necessary
			auto xopt = subst.get(x);
			if( xopt.has_value() ) {
				avoids[1].insert(x);// this lhs cannot be unified with rhs containing x
				unify(*xopt,r);
				avoids[1].erase(x);
				return;
			}
			if( fvar(x) ) {// local variables can be assigned
				StrSet bounds;
				subst.assign(x,sanitize(r,bounds,avoids[1],escapes[1]));
				return;
			}
			return unify1(x,r);
		}
		unify2(l,r,index);
	}
	CSubst result() {
		StrSet done;
		for( auto& x : subst.map() ) {
			subst.assign(x.first,subst.get(x.first)->subst(subst));
		}
		return subst;
	}
};

optional<CSubst> unify(CTerm const& l, CTerm const& r, std::function<bool(String const&)> const& fvar) {
	if( r.ctxt() != l.ctxt() ) {
		throw WrongContext();
	}
	Unifier u = Unifier(l.ctxt(),fvar);
	try {
		u.unify(l,r);
		return u.result();
	} catch( exception const& e ) {
		return optional<CSubst>();
	}
}
