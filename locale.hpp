#ifndef _LOCALE_HPP
#define _LOCALE_HPP
#include<map>
#include"core.hpp"
#include"syntax.hpp"

class Import;
using Imports = std::multimap<std::string,Import,std::less<>>;

class Locale : public Ctxt {
	struct _Body;
	Ref<_Body> _ref;
	Locale( Ref<_Body> const& ref, Ctxt const& ctxt ) : _ref(ref), Ctxt(ctxt) {}
public:
	struct Error : public ::Error {
		Error(Term const& term) : ::Error(term) {}
	};
	Locale();
	/** Creates a branch locale. */
	Locale branch() const;
	/** Obtains the parent locale. */
	Opt<Locale> parent() const;
	/** @brief Local theorems.
	 * 
	 * @return map from the theorem names to the statements.
	 */
	StrMap<Thm const> const& thms() const&;
	/** @brief Finds a named theorem from the locale or an ancestor. */
	Opt<Thm> find_thm(std::string_view const& name, bool ancestor = true) const;
	/** @brief Finds a named theorem with prefix from the locale or an ancestor. */
	Opt<Thm> find_thm(std::string_view const& pre, std::string_view const& name, bool ancestor = true) const;
	/** @brief Obtains a named theorem from the locale or an ancestor.
	 * @exception TheoremNotFound is thrown if the name doesn't match any.
	 */
	Thm thm(std::string_view const& name) const {
		if( auto opt = find_thm(name) ) {
			return *opt;
		}
		throw TheoremNotFound(name);
	}
	/** @brief Adds a named theorem in the locale.
	 * @exception is thrown if the theorem doesn't belong to this locale
	 */
	void add_thm(std::string_view const& name, Thm const& thm) &;
	void assume(std::string_view const& name, Term const& assm) & {
		add_thm(name,Ctxt::assume(assm));
	}
	template<class I>
	void obtain(Thm const& thm, I name_it) & {
		auto [sym,props] = Ctxt::obtain(thm);
		for( Thm& prop : props ) {
			add_thm(*name_it,prop);
			name_it++;
		}
	}
	/** Declares sublocale */
	Import& import(std::string&& name, Locale const& loc) &;
	/** multimap of sublocales */
	Imports const& imports() const &;
	/** Pretty printer for context */
	std::function<std::ostream& (std::ostream&)> const pretty(Syntax const& syntax) const &;
	std::function<std::ostream& (std::ostream&)> const pretty(Syntax&& syntax) = delete;
};

struct Locale::_Body {
	Opt<Locale> parent;
	StrMap<Thm const> thms;
	std::multimap<std::string,Import,std::less<>> imports;
	_Body() {}
	_Body(Opt<Locale> parent) : parent(parent) {}
};

class Import : public Intp {
	Locale _locale;
	Import(Import const&) = delete;
public:
	Import( Ctxt const& ctxt, Locale const& loc ) :
		Intp(Intp::make(loc,ctxt)), _locale(loc) {
	}
	/**
	 * @brief Obtains a theorem in the sublocale.
	 * 
	 * @param name 
	 * @return Opt<Thm> 
	 */
	Opt<Thm> find_thm(std::string_view const& name) const {
		if( auto thm = _locale.find_thm(name,false) ) {
			return subst(*thm);
		}
		return {};
	}
};

inline Locale::Locale() : _ref(Ref<_Body>::make()) {};
inline Locale Locale::branch() const {
	return Locale(Ref<_Body>::make(*this), Ctxt::branch());
}
inline Opt<Locale> Locale::parent() const {
	return _ref->parent;
}
inline StrMap<Thm const> const& Locale::thms() const& {
	return _ref->thms;
}
inline void Locale::add_thm(std::string_view const& name, Thm const& thm) & {
	if( thm.ctxt() != *this ) {
		throw Error(Term("#locale")(Term("add_thm")));
	}
	_ref->thms.emplace(name,thm);
}
inline Imports const& Locale::imports() const & {
	return _ref->imports;
}

inline std::ostream& operator<<(std::ostream& os, Locale const& loc) {
	return os << loc.pretty(SYNTAX);
}

inline Import& Locale::import(std::string&& name, Locale const& loc) & {
	auto it = _ref->imports.emplace(std::piecewise_construct,
		std::make_tuple(std::move(name)),
		std::forward_as_tuple(*this,loc)
	);
	return it->second;
};

#endif