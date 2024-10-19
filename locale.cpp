#include"locale.hpp"

using namespace std;

Opt<Thm> Locale::find_thm(string_view const& name, bool ancestor) const {
	if( auto sep = name.find('.'); sep != string::npos ) {
		return find_thm(name.substr(0,sep),name.substr(sep+1),ancestor);
	} else {
		if( auto opt = _ref->thms.finds(name) ) {
			return opt->second;
		}
		if( auto ret = find_thm("",name,false) ) {
			return ret;
		}
		if( ancestor && _ref->parent ) {
			if( auto opt = _ref->parent->find_thm(name) ) {
				return opt->weaken(*this);
			}
		}
	}
	return {};
}

Opt<Thm> Locale::find_thm(std::string_view const& pre, std::string_view const& name, bool ancestor) const {
	auto [it,end] = _ref->imports.equal_range(pre);
	while( it != end ) {
		if( auto opt = it->second.find_thm(name) ) {
			return opt;
		}
		it++;
	}
	if( ancestor && _ref->parent ) {
		if( auto opt = _ref->parent->find_thm(pre,name,ancestor) ) {
			return opt->weaken(*this);
		}
	}
	return {};
}

function<ostream& (ostream&)> const Locale::pretty(Syntax const& syntax) const & {
	return [&](ostream& os)->ostream& {
		os << "{\n" << *(Ctxt*)this;
		for( auto& [name,thm] : _ref->thms ) {
			os << "\tthm " << name << ": " << thm << ';' << endl;
		}
		return os << "}";
	};
}
