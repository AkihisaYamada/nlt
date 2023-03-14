#ifndef _STRING_HPP_
#define _STRING_HPP_

#include<string>
#include<string_view>
#include<iostream>
#include"ref.hpp"

static std::string const EMPTY = "";

class String : public Safe<std::string> {
public:
	String() : Safe(EMPTY) {}
	String( std::string&& val ) : Safe(std::move(val)) {}
	String( std::string_view val ) : Safe(std::string(val)) {}
	String( char const* val ) : Safe(val) {}
};

inline bool operator<(String const& l, String const& r) {
	return *l < *r;
};
inline bool operator<(String const& l, std::string_view const& r) {
	return *l < r;
};
inline bool operator<(std::string_view const& l, String const& r) {
	return l < *r;
};
inline std::ostream& operator<<(std::ostream& os, String const& x) {
	return os << *x;
}

#endif
