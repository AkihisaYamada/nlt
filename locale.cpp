#include"locale.hpp"

using namespace std;

Opt<Thm> Locale::find_thm(string_view const& name, bool ancestor) const {
	if( auto sep = name.find('.'); sep != string::npos ) {
		return find_thm(name.substr(0,sep),name.substr(sep+1),ancestor);
	} else {
		if( auto opt = _thms.finds(name) ) {
			return opt->second;
		}
		if( ancestor && _parent ) {
			if( auto opt = (**_parent).find_thm(name) ) {
				return opt->weaken(_ctxt);
			}
		}
	}
	return {};
}

Opt<Thm> Locale::find_thm(std::string_view const& pre, std::string_view const& name, bool ancestor) const {
	auto [it,end] = _sublocs.equal_range(pre);
	while( it != end ) {
		if( auto opt = it->second.find_thm(name) ) {
			return opt;
		}
		it++;
	}
	if( ancestor && _parent ) {
		return (**_parent).find_thm(pre,name);
	}
	return {};
}
