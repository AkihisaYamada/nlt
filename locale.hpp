#ifndef _LOCALE_HPP
#define _LOCALE_HPP
#include<map>
#include"core.hpp"
#include"syntax.hpp"

class Sublocale;

class Locale {
	Opt<Ref<Locale const>> _parent;
	Ref<Syntax> _syntax;
	Ctxt _ctxt;
	StrMap<Thm const> _thms;
	StrMap<Sublocale const> _sublocs;
public:
	Locale() : _syntax( Ref<Syntax>::make() ) {}
	/**
	 * @brief Local theorems.
	 * 
	 * @return map from the theorem names to the statements.
	 */
	StrMap<Thm const> const& thms() const& {
		return _thms;
	}
	/**
	 * @brief Obtains a named theorem from the context or an ancestor.
	 */
	Opt<Thm> find_thm(std::string const& name) const {
		if( auto opt = _thms.finds(name) ) {
			return opt->second;
		}
		if( _parent ) {
			if( auto opt = (*_parent)->find_thm(name) ) {
				return *opt;
			}
		}
		return {};
	}
	/**
	 * @brief Obtains a named theorem from the locale or an ancestor.
	 * @exception TheoremNotFound is thrown if the name doesn't match any.
	 */
	Thm thm(std::string const& name) const {
		if( auto opt = find_thm(name) ) {
			return *opt;
		}
		throw TheoremNotFound(name);
	}
	/**
	 * @brief Adds a named theorem in the locale.
	 * @exception WrongContext is thrown if the theorem doesn't belong to this context
	 */
	Locale& add_thm(std::string const& name, Thm const& thm) {
		if( thm.ctxt() != _ctxt ) {
			throw WrongContext();
		}
		_thms.emplace(name,thm);
		return *this;
	}

};

#endif