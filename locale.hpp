#ifndef _LOCALE_HPP
#define _LOCALE_HPP
#include<map>
#include"util.hpp"
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
	struct TheoremNotFound : public Error {
		TheoremNotFound(std::string_view const& name) :
			Error(Term("#theorem_not_found")(name)) {}
	};
	Locale();
	/** Creates an anonymous branch locale. */
	Locale branch() const;
	/** Creates a named branch. */
	Locale branch(std::string_view const& name);
	/** Obtains the parent locale. */
	Opt<Locale const> parent() const;
	/** @brief Local theorems.
	 * 
	 * @return map from the theorem names to the statements.
	 */
	StrMap<Thm const> const& thms() const;
	/** @brief Finds a named theorem from the locale or an ancestor. */
	Opt<Thm> find_thm(std::string_view const& name, bool ancestor = true) const;
	/** @brief Finds a named theorem with prefix from the locale or an ancestor. */
	Opt<Thm> find_thm(std::string_view const& pre, std::string_view const& name) const;
	/** @brief Obtains a named theorem from the locale.
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
	void add_thm(std::string_view const& name, Thm const& thm);
	/** adds to locale discharge database */
	void add_discharge_thm( Thm const& thm );
	/** finds in locale discharge database */
	Opt<Thm> find_discharge_thm( Term const& thm ) const {
		if( auto const& ret = _find_discharge_thm(thm) ) {
			return ret;
		}
		return _find_discharge_thm(thm,*this);
	}
	/** Assuming a closed term. */
	void assume(std::string_view const& name, CTerm const& assm) {
		Thm const& thm = Ctxt::assume(assm);
		add_thm(name,thm);
		add_discharge_thm(thm);
	}
	/** Declares import */
	Import& import(std::string&& name, Locale const& loc) &;
	/** Declares import */
	Import& import(std::string_view const& name, Locale const& loc) & {
		return import(std::string(name),loc);
	}
	/** multimap of imports */
	Imports const& imports() const;
	/** Finds branch locale */
	Opt<Locale> find_locale(std::string_view const& name, bool ancestor = true) const;
	Locale locale(std::string_view const& name) const {
		if( auto x = find_locale(name) ) {
			return *x;
		}
		throw Error(Term("#locale_not_found")(name));
	}
	/** Pretty printer for context */
	std::function<std::ostream& (std::ostream&)> const pretty(Syntax const& syntax, size_t indent = 0) const &;
	std::function<std::ostream& (std::ostream&)> const pretty(Syntax&& syntax) = delete;
private:
	Opt<Thm> _find_discharge_thm( Term const& thm ) const;
	Opt<Thm> _find_discharge_thm( Term const& thm, Ctxt const& orig ) const;
};

struct Locale::_Body {
	Opt<Locale const> parent;
	StrMap<Thm const> thms;
	StrMap<Locale const> locales;
	std::set<Thm,std::less<>> locale_thms;
	std::multimap<std::string,Import,std::less<>> imports;
	_Body() {}
	_Body(Opt<Locale const> parent) : parent(parent) {}
};

class Import : public Intp {
	Locale const _src;
	Locale _tgt;
public:
	/** creates import
	 * @param src the locale to be interpreted
	 * @param tgt the locale that interprets src
	 */
	Import( Locale const& tgt, Locale const& src ) :
		Intp(Intp::make(src,tgt)), _src(src), _tgt(tgt) {
	}
	Locale const& source() const& {
		return _src;
	}
	Locale& target() & {
		return _tgt;
	}
	/** automatic instantiation */
	bool instantiates() {
		auto v = fixing();
		if( !v ) return false;
		auto t = _tgt.constant(*v);
		if( !t ) throw Error("\"instantiation must be specified\"")(*v);
		instantiate(*t);
		return true;
	}
	/** automatic instantiation */
	bool imports_fix() {
		auto v = fixing();
		if( !v ) return false;
		auto t = _tgt.constant(*v);
		instantiate( t ? *t : _tgt.fix(*v) );
		return true;
	}
	/** discharge assumption and remember it for later automation */
	void discharge( Thm const& thm ) & {
		Intp::discharge(thm);
		_tgt.add_discharge_thm(thm);
	}
	/** discharge assumption by knowledge */
	bool discharges() & {
		auto assm = assuming();
		if( !assm ) {
			return false;
		}
		// if this assumption is already discharged, then reuse it
		auto opt = _tgt.find_discharge_thm(*assm);
		if( !opt ) {
			throw Error("\"failed know\"");
		}
		Intp::discharge(*opt);
		return true;
	}
	void discharge() & {
		if( !discharges() ) {
			throw Error("\"unexpected know\"");
		}
	}
	/** discharges or imports assumption */
	bool imports_assume() & {
		auto assm = assuming();
		if( !assm ) {
			return false;
		}
		// if this assumption is already discharged, then reuse it
		if( auto opt = _tgt.find_discharge_thm(*assm) ) {
			Intp::discharge(*opt);
		} else { // otherwise, make new assumption;
			auto thm = _tgt.Ctxt::assume(*assm);
			discharge(thm);
		}
		return true;
	}
	/** retain constant and remember it for later automation */
	void retain( CTerm c, Thm const& thm ) & {
		Intp::retain(c,thm);
		_tgt.add_discharge_thm(thm);
	}
	void retain( CTerm c ) {
		auto o = obtaining();
		if( !o ) {
			throw Error(c);
		}
		auto [sym,ex,spec] = *o;
		auto const& thm = _tgt.find_discharge_thm(spec.inst(c));
		if(!thm) {
			throw Error(sym)(c);
		}
		Intp::retain(c,*thm);
	}
	/** automatic retain */
	bool retains() {
		auto o = obtaining();
		if( !o ) {
			return false;
		}
		auto [sym,ex,spec] = *o;
		if( auto csym = _tgt.constant(sym) ) {
			if( auto const& thm = _tgt.find_discharge_thm(spec.inst(*csym)) ) {
				Intp::retain(*csym,*thm);
				return true;
			}
			throw MalformedRetain(sym);
		} else {
			auto [sym_term,spec] = _tgt.obtain(sym,ex);
			retain(sym_term,spec);
			_tgt.add_discharge_thm(spec);
			return true;
		}
	}
	/**
	 * @brief Obtains a theorem in the interpretation.
	 * 
	 * @param name 
	 * @return Opt<Thm> 
	 */
	Opt<Thm> find_thm(std::string_view const& name) const {
		if( auto thm = _src.find_thm(name,false) ) {
			return subst(*thm);
		}
		return {};
	}
};

inline Locale::Locale() : _ref(Ref<_Body>::make()) {};
inline Locale Locale::branch() const {
	return Locale(Ref<_Body>::make(Opt<Locale const>(*this)), Ctxt::branch());
}
inline Locale Locale::branch( std::string_view const& name ) {
	return _ref->locales.emplace(name,branch()).first->second;
}
inline Opt<Locale const> Locale::parent() const {
	return _ref->parent;
}
inline StrMap<Thm const> const& Locale::thms() const {
	return _ref->thms;
}
inline void Locale::add_thm(std::string_view const& name, Thm const& thm) {
	if( thm.ctxt() != *this ) {
		throw Error(Term("#locale")("add_thm")(thm));
	}
	_ref->thms.emplace(name,thm);
}
inline void Locale::add_discharge_thm( Thm const& thm ) {
	_ref->locale_thms.insert(thm);
}

inline Imports const& Locale::imports() const {
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