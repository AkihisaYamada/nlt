#include"locale.hpp"

using namespace std;

Locale::Error const Locale::LocaleNotFound = Error("\"locale not found\"");

std::function<Thm(Thm const&)> const Locale::_triv_proc =
	[]( Thm const& thm ) { return thm; };

std::function<bool(AThm const&)> const Locale::_triv_test =
	[]( AThm const& ) { return true; };

AThm Locale::add_assm(std::string_view const& name, CTerm const& assm) {
	size_t rev = revision();
	auto const& thm = add_thm(name,Ctxt::assume(assm));
	_ref->assm_names.emplace(rev,name);
	return thm;
}

AThm Locale::add_thm(std::string_view const& name, Thm const& thm) {
	if( thm.ctxt() != *this ) {
		throw Error(Term("#locale")("add_thm")(thm));
	}
	auto const& [thm2,info] = _ref->thms.emplace(name,std::pair(thm,ThmInfo()))->second;
	return AThm(*this,thm,info);
}

pair<CTerm,Thm> Locale::obtain( std::string_view const& sym, Thm const& ex, std::string_view const& spec_name ) {
	size_t rev = revision();
	auto const& ret = Ctxt::obtain(sym,ex);
	add_thm(spec_name,ret.second);
	_ref->assm_names.emplace(rev,spec_name);
	return ret;
}
Opt<AThm> Locale::_find_thm(
	std::string_view const& name,
	std::function<Thm(Thm const&)> const& proc,
	std::function<bool(AThm const&)> const& test,
	bool ancestor,
	bool noprefix,
	Locale const& orig
) const {
	for( auto [it,end] = _ref->thms.equal_range(name); it != end; it++ ) {
		auto const& ret = AThm(orig,proc(it->second.first),it->second.second);
		if( test(ret) ) {// found in the current locale
			return ret;
		}
	}
	if( noprefix ) {
		for( auto const& [pre,imp] : _ref->imports ) {
			if( auto const& ret = imp._find_thm(name,proc,test,noprefix,orig) ) {
				return ret;
			}
		}
	} else {
		if( auto ret = _find_thm("",name,proc,test,orig) ) {// unnamed import
			return ret;
		}
		if( auto sep = name.find('.'); sep != string::npos ) {// named imports
			if( sep == 0 ) {// explicit parent
				if( auto opt = _ref->parent ) {
					return opt->_find_thm(name.substr(sep+1),proc,test,ancestor,noprefix,orig);
				}
				throw Error("\"parent locale not found\"");
			}
			if( auto ret = _find_thm(name.substr(0,sep),name.substr(sep+1),proc,test,orig) ) {
				return ret;
			}
		}
	}
	if( ancestor )
	if( auto p = _ref->parent ) {
		auto const& proc2 = [&]( Thm const& thm ) {
			return proc(thm.weaken(*this));
		};
		return p->_find_thm(name,proc2,test,ancestor,noprefix,orig);
	}
	return {};
}
Opt<AThm> Locale::_find_thm(
	std::string_view const& pre,
	std::string_view const& name,
	std::function<Thm(Thm const&)> const& proc,
	std::function<bool(AThm const&)> const& test,
	Locale const& orig
) const {
	// pre as interpretations
	for( auto [it,end] = _ref->imports.equal_range(pre); it != end; it++ ) {
		if( auto opt = it->second._find_thm(name,proc,test,false,orig) ) {
			return opt;
		}
	}
	return {};
}
Opt<AThm> Import::_find_thm(
	std::string_view const& name,
	std::function<Thm(Thm const&)> const& proc,
	std::function<bool(AThm const&)> const& test,
	bool noprefix,
	Locale const& orig
) const {
	if( ready() ) {// only find if the interpretation is ready
		auto const& proc2 = [&]( Thm const& thm ){
			return proc(Intp::subst(thm));
		};
		return _src._find_thm(name,proc2,test,false,noprefix,orig);
	}
	return {};
}
Opt<Locale> Locale::find_locale(string_view const &name, bool ancestor) const {
	if( size_t sep = name.find('.'); sep != string::npos ) {
		if( auto const& p = _ref->parent ) {
			return p->find_locale(name.substr(sep+1));
		}
		throw LocaleNotFound(".");
	}
	if( auto ret = _ref->locales.finds(name) ) {
		return ret->second;
	}
	if( ancestor ) {
		if( auto& parent = _ref->parent ) {
			return parent->find_locale(name,true);
		}
	}
	return {};
}

auto _test_term_eq( Term const& x ) {
	return [&]( Term const& y ) { return x == y; };
}
bool Import::discharges( bool mod ) {
	auto x = assuming();
	if( !x ) {
		return false;
	}
	auto [name,assm] = *x;
	// if this assumption is already discharged, then reuse it
	if( auto opt = _tgt.find_thm(name,_test_term_eq(assm),true,true) ) {
		Intp::discharge(*opt);
		return true;
	} else if( mod ) { // if modification is allowed, then make new assumption
		auto thm = _tgt.add_assm(name,assm);
		Intp::discharge(thm);
		return true;
	} else {
		throw Error("\"failed know\"")(name)(assm);
	}
}

void Import::retain( CTerm c ) {
	auto o = obtaining();
	if( !o ) {
		throw Error(c);
	}
	auto [name,sym,ex,spec] = *o;
	Term const& stmt = spec.inst(c);
	auto const& thm = _tgt.find_thm(name,_test_term_eq(stmt),true,true);
	if(!thm) {
		throw Error(sym)(c);
	}
	Intp::retain(c,*thm);
}

bool Import::retains() {
	auto o = obtaining();
	if( !o ) {
		return false;
	}
	auto [name,sym,ex,spec] = *o;
	if( auto csym = _tgt.constant(sym) ) {
		Term const& stmt = spec.inst(*csym);
		if( auto const& thm = _tgt.find_thm(name,_test_term_eq(stmt),true,true) ) {
			Intp::retain(*csym,*thm);
			return true;
		}
		throw MalformedRetain(sym)(name)(stmt);
	} else {
		auto [sym_term,spec] = _tgt.obtain(sym,ex,name);
		retain(sym_term,spec);
		return true;
	}
}


static ostream& mk_indent(ostream& os, size_t n) {
	for( size_t i = 0; i < n; i++ ) {
		os << "  ";
	}
	return os;
}
function<ostream&(ostream&)> const Locale::print_name( Syntax const& syntax ) const& {
	return [&](ostream& os)->ostream& {
		os << _ref->name;
		if( syntax.prints_ctxt() ) {
			os << '@' << id() << ' ';
		}
		return os;
	};
}

function<ostream&(ostream&)> const Locale::pretty(Syntax const& syntax, size_t n) const & {
	return [&](ostream& os)->ostream& {
		os << "locale " << print_name(syntax);
		if( parent() ) {
			os << " <- " << parent()->print_name(syntax);
		}
		os << " {" << endl;
		n++;
		for( size_t i = 0; i < revision(); i++ ) {
			if( auto str = fixed(i) ) {
				mk_indent(os,n) << "fixes " << *str << endl;
			} else if( auto assm = assumed(i) ) {
				mk_indent(os,n) << "assumes " << syntax.pretty_thm(*assm) << endl;
			} else if( auto obt = obtained(i) ) {
				auto [sym,ex,spec] = *obt;
				mk_indent(os,n) << "obtains " << sym << " in " << syntax.pretty_thm(spec) << endl;
			} else {
				assert(false);
			}
		}
		for( auto& [name,imp] : _ref->imports ) {
			mk_indent(os,n) << "imports " << name << ": " << imp.source().print_name(syntax) << "..." << endl;
		}
		for( auto& [name,thm] : _ref->thms ) {
			mk_indent(os,n) << "thm " << name << ": " << syntax.pretty_thm(thm.first) << ';' << endl;
		}
		for( auto& [name,loc] : _ref->locales ) {
			mk_indent(os,n) << "locale " << name << ": " << loc.pretty(syntax,n) << endl;
		}
		n--;
		return mk_indent(os,n) << "}";
	};
}
