#include"locale.hpp"

using namespace std;

Opt<Thm> Locale::find_thm(string_view const& name, bool ancestor) const {
	if( auto opt = _ref->thms.finds(name) ) {// current locale
		return opt->second;
	}
	if( auto ret = find_thm("",name) ) {// unnamed import or child locale
		return ret;
	}
	if( ancestor && _ref->parent ) {
		if( auto opt = _ref->parent->find_thm(name) ) {// parent
			auto ret = opt->weaken(*this);
			return ret;
		}
	}
	if( auto sep = name.find('.'); sep != string::npos ) {// named imports
		return find_thm(name.substr(0,sep),name.substr(sep+1));
	}
	return {};
}

Opt<Thm> Locale::find_thm(string_view const& pre, string_view const& name) const {
	// pre as interpretations
	auto [it,end] = _ref->imports.equal_range(pre);
	while( it != end ) {
		if( auto opt = it->second.find_thm(name) ) {
			return opt;
		}
		it++;
	}
	// pre as child locales
	if( auto loc = find_locale(pre,false) ) {
		if( auto thm = loc->find_thm(name,false) ) {
			Thm ret = thm->intro();
			return ret;
		}
	}
	return {};
}

Opt<Locale> Locale::find_locale(string_view const &name, bool ancestor) const {
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

static ostream& mk_indent(ostream& os, size_t n) {
	for( size_t i = 0; i < n; i++ ) {
		os << "  ";
	}
	return os;
}
function<ostream& (ostream&)> const Locale::pretty(Syntax const& syntax, size_t n) const & {
	return [&](ostream& os)->ostream& {
		if( syntax.prints_ctxt() ) {
			os << '@' << id() << ' ';
			if( parent() ) {
				os << "<- @" << parent()->id() << ' ';
			}
		}
		os << "{" << endl;
		n++;
		for( size_t i = 0; i < revision(); i++ ) {
			if( auto str = fixed(i) ) {
				mk_indent(os,n) << "fixes " << *str << endl;
			} else if( auto assm = assumed(i) ) {
				mk_indent(os,n) << "assumes " << syntax.pretty_thm(*assm) << endl;
			} else if( auto obt = obtained(i) ) {
				mk_indent(os,n) << "obtains " << syntax.pretty_thm(*obt) << endl;
			} else {
				assert(false);
			}
		}
		for( auto& [name,thm] : _ref->thms ) {
			mk_indent(os,n) << "thm " << name << ": " << syntax.pretty_thm(thm) << ';' << endl;
		}
		for( auto& [name,loc] : _ref->locales ) {
			mk_indent(os,n) << "locale " << name << ": " << loc.pretty(syntax,n) << endl;
		}
		n--;
		return mk_indent(os,n) << "}";
	};
}
