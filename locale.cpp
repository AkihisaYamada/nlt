#include"locale.hpp"

using namespace std;

Locale::Error const Locale::LocaleNotFound = Error("\"locale not found\"");

AThm Locale::assume(std::string_view const& name, CTerm const& assm) {
	size_t rev = revision();
	auto const& thm = add_thm(name,Ctxt::assume(assm));
	_ref->assm_names.emplace(rev,name);
	return thm;
}

AThm Locale::add_thm(std::string_view const& name, Thm const& thm) {
	if( thm.ctxt() != *this ) {
		throw Error(Term("#locale")("add_thm")(thm));
	}
	auto const& it = _ref->thms.emplace(name,std::pair(thm,ThmInfo()));
	return AThm(*this,it.first->second);
}

pair<CTerm,Thm> Locale::obtain( std::string_view const& sym, Thm const& ex, std::string_view const& spec_name ) {
	size_t rev = revision();
	auto const& ret = Ctxt::obtain(sym,ex);
	add_thm(spec_name,ret.second);
	_ref->assm_names.emplace(rev,spec_name);
	return ret;
}

Opt<AThm> Locale::find_thm(
	string_view const& name,
	Opt<std::function<bool(Thm const&)>> test,
	bool ancestor,
	bool noprefix
) const {
	if( auto opt = _ref->thms.finds(name) )
	if( !test || (*test)(opt->second.first) ) {// found in the current locale
		return AThm(*this,opt->second);
	}
	if( noprefix ) {
		for( auto const& [pre,imp] : _ref->imports ) {
			if( auto const& ret = imp.find_thm(name,test,noprefix) ) {
				return ret;
			}
		}
	} else {
		if( auto ret = find_thm("",name,test) ) {// unnamed import
			return ret;
		}
		if( auto sep = name.find('.'); sep != string::npos ) {// named imports
			if( sep == 0 ) {// explicit parent
				if( auto opt = _ref->parent ) {
					return opt->find_thm(name.substr(sep+1),test);
				}
				throw Error("\"parent locale not found\"");
			}
			if( auto ret = find_thm(name.substr(0,sep),name.substr(sep+1),test) ) {
				return ret;
			}
		}
	}
	if( ancestor )
	if( auto p = _ref->parent )
	if( auto opt = p->find_thm(name,test,ancestor,noprefix) ) {// parent
		return opt->weaken(*this);
	}
	return {};
}

Opt<AThm> Locale::find_thm(
	string_view const& pre,
	string_view const& name,
	Opt<std::function<bool(Thm const&)>> test
) const {
	// pre as interpretations
	for( auto [it,end] = _ref->imports.equal_range(pre); it != end; it++ ) {
		if( auto opt = it->second.find_thm(name,test,false) ) {
			return opt;
		}
	}
	return {};
}

Opt<AThm> Import::find_thm(
	std::string_view const& name,
	Opt<std::function<bool(Thm const&)> const&> test,
	bool noprefix
) const {
	if( ready() ) {// only find if the interpretation is ready
		if( test ) {
			auto const& test2 = [&]( Thm const& thm ){
				return (*test)(Intp::subst(thm));
			};
			if( auto const& thm = _src.find_thm(name,test2,false,noprefix) ) {
				return subst(*thm);
			}
		} else {
			if( auto const& thm = _src.find_thm(name,{},false,noprefix) ) {
				return subst(*thm);
			}
		}
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

bool Import::discharges( bool mod ) {
	auto x = assuming();
	if( !x ) {
		return false;
	}
	auto [name,assm] = *x;
	// if this assumption is already discharged, then reuse it
	if( auto opt = _tgt.find_thm(name,[&](Thm const& thm){ return (Term)assm == thm; },true,true) ) {
		Intp::discharge(*opt);
		return true;
	} else if( mod ) { // if modification is allowed, then make new assumption
		auto thm = _tgt.assume(name,assm);
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
	auto const& thm = _tgt.find_thm(name,[&](Thm const& thm){ return thm == stmt; },true,true);
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
		if( auto const& thm = _tgt.find_thm(name,[&](Thm const& thm){ return thm == stmt; },true,true) ) {
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
