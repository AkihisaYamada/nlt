#ifndef _STRING_HPP_
#define _STRING_HPP_

#include <string>
#include <iostream>
#include "ref.hpp"

class String {
	Ref<std::string const> _ref;
	void operator*() = delete;
public:
	String() : _ref() {}
	String(char const* str) : _ref(str) {}
	String(std::string&& str) : _ref(str) {}
	String(String const& other) : _ref(other._ref) {}
	String& operator=(char const* str) {
		_ref = Ref<std::string const>(str);
		return *this;
	}
	String& operator=(String const& other) {
		_ref = other._ref;
		return *this;
	}
	operator std::string const& () const {
		return *_ref;
	};
	friend bool operator==(String const& l, String const& r);
};

inline bool operator==(String const& l, String const& r) {
	return l._ref == r._ref || *l._ref == *r._ref;
};
inline bool operator==(String const& l, char const* r) {
	return (std::string const&)l == r;
};
inline bool operator<(String const& l, String const& r) {
	return (std::string const&)l < (std::string const&)r;
};
inline bool operator<(std::string_view const& l, String const& r) {
	return l < (std::string const&)r;
};
inline bool operator<(String const& l, std::string_view const& r) {
	return (std::string const&)l < r;
};

inline std::ostream& operator<<(std::ostream& os, String const& x) {
	return os << (std::string const&)x;
}

#endif
