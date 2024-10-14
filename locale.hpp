#ifndef _LOCALE_HPP
#define _LOCALE_HPP
#include<map>
#include"core.hpp"
#include"syntax.hpp"

class SubLocale;

class Locale {
	struct Error : public ::Error {
		Error(Term const& term) : ::Error(term) {}
	};
	Opt<Ref<Locale>> _parent;
	Ctxt _ctxt;
	StrMap<Thm const> _thms;
	std::multimap<std::string, SubLocale const,std::less<>> _sublocs;
public:
	Locale() {}
	/** Creates a branch locale. */
	Locale( Ref<Locale> const& parent ) : _parent(parent), _ctxt(parent->_ctxt.branch()) {}
	Ref<Locale const> const& parent() const & {
		if( !_parent ) {
			throw Error(Term("#locale"));
		}
		return *_parent;
	}
	Ref<Locale> const& parent() & {
		if( !_parent ) {
			throw Error(Term("#locale"));
		}
		return *_parent;
	}
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
	 * @brief Finds a named theorem from the locale or an ancestor.
	 */
	Opt<Thm> find_thm(std::string_view const& name, bool ancestor = true) const;
	/**
	 * @brief Finds a named theorem with prefix from the locale or an ancestor.
	 */
	Opt<Thm> find_thm(std::string_view const& pre, std::string_view const& name, bool ancestor = true) const;
	/**
	 * @brief Obtains a named theorem from the locale or an ancestor.
	 * @exception TheoremNotFound is thrown if the name doesn't match any.
	 */
	Thm thm(std::string_view const& name) const {
		if( auto opt = find_thm(name) ) {
			return *opt;
		}
		throw TheoremNotFound(name);
	}
	/**
	 * @brief Adds a named theorem in the locale.
	 * @exception is thrown if the theorem doesn't belong to this locale
	 */
	Locale& add_thm(std::string_view const& name, Thm const& thm) & {
		if( thm.ctxt() != _ctxt ) {
			throw Error(Term("#locale")(Term("add_thm")));
		}
		_thms.emplace(name,thm);
		return *this;
	}

	Locale& fix(std::string_view const& sym) & {
		_ctxt.fix(sym);
		return *this;
	}
	Locale& assume(std::string_view const& name, Term const& assm) & {
		add_thm(name,_ctxt.assume(assm));
		return *this;
	}
	template<class I>
	Locale& obtain(Thm const& thm, I name_it) & {
		for( Thm& prop : _ctxt.obtain(thm) ) {
			add_thm(*name_it,prop);
			name_it++;
		}
		return *this;
	}
	void sublocale(std::string_view const& name, Locale const& loc) &;
};

class SubLocale {
	Intp _intp;
	Ref<Locale> _locale;
public:
	SubLocale( Ctxt const& ctxt, Ref<Locale> const& loc ) :
		_intp(Intp::make(loc->ctxt(),ctxt)), _locale(loc) {
	}
	/**
	 * @brief Obtains a theorem in the sublocale.
	 * 
	 * @param name 
	 * @return Opt<Thm> 
	 */
	Opt<Thm> find_thm(std::string_view const& name) const {
		if( auto thm = _locale->find_thm(name,false) ) {
			return _intp.subst(*thm);
		}
		return {};
	}
};

#endif