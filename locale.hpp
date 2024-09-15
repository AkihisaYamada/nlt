#ifndef _LOCALE_HPP
#define _LOCALE_HPP
#include<map>
#include"core.hpp"
#include"syntax.hpp"

class Sublocale;

class Locale : public Syntax {
	Opt<Locale const> _parent;
	Ctxt _ctxt;
	StrMap<Thm const> _thms;
	StrMap<Sublocale const> _sublocs;
	Locale( Locale const& parent );
public:
	Locale();
	Ref<Locale> branch() const &;
	Ref<Locale>& parent() &;
	Ref<Locale> const& parent() const &;
	Ctxt& ctxt() & {
		return _ctxt;
	}
	Ctxt const& ctxt() const & {
		return _ctxt;
	}
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
			if( auto opt = _parent->find_thm(name) ) {
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
	 * @exception WrongContext is thrown if the theorem doesn't belong to this locale
	 */
	Locale& add_thm(std::string const& name, Thm const& thm) {
		if( thm.ctxt() != _ctxt ) {
			throw WrongContext("add_thm");
		}
		_thms.emplace(name,thm);
		return *this;
	}

	Locale& fix(std::string const& sym) {
		_ctxt.fix(sym);
		return *this;
	}
	Locale& assume(std::string const& name, Term const& assm) {
		add_thm(name,_ctxt.assume(assm));
		return *this;
	}
	template<class I>
	Locale& obtain(Thm const& thm, I name_it) {
		for( Thm& prop : _ctxt.obtain(thm) ) {
			add_thm(*name_it,prop);
			name_it++;
		}
		return *this;
	}
};


#endif