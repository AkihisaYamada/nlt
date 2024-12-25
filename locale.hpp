#ifndef _LOCALE_HPP
#define _LOCALE_HPP
#include<map>
#include"util.hpp"
#include"syntax.hpp"

class Import;
using Imports = std::multimap<std::string,Import,std::less<>>;

inline std::string make_spec_name( std::string base ) {
	return std::move(base)+"$spec";
}

class Locale : public Ctxt {
	struct _Body;
	Ref<_Body> _ref;
	Locale( Ref<_Body> const& ref, Ctxt const& ctxt ) : _ref(ref), Ctxt(ctxt) {}
public:
	struct Error : public ::Error {
		Error(Term const& term) : ::Error(term) {}
	};
	static Error const LocaleNotFound;
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
	Opt<Thm> find_thm(
		std::string_view const& name,
		Opt<std::function<bool(Thm const&)>> test = {},
		bool ancestor = true,
		bool noprefix = false
	) const;
	/** @brief Finds a named theorem with prefix from the locale or an ancestor. */
	Opt<Thm> find_thm(
		std::string_view const& pre,
		std::string_view const& name,
		Opt<std::function<bool(Thm const&)>> test = {}
	) const;
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
	/** finds the name of assumption made in the revision */
	Opt<std::string> find_assm_name( size_t rev ) const;
	/** Assuming a closed term. */
	Thm assume(std::string_view const& name, CTerm const& assm);
	std::pair<CTerm,Thm> obtain( std::string_view const& sym, Thm const& ex, std::string_view const& spec_name );
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
	std::function<std::ostream&(std::ostream&)> const pretty(Syntax const& syntax, size_t indent = 0) const &;
	std::function<std::ostream&(std::ostream&)> const pretty(Syntax&&,size_t) = delete;
	std::function<std::ostream&(std::ostream&)> const print_name(Syntax const& syntax) const&;
	std::function<std::ostream&(std::ostream&)> const print_name(Syntax&&) = delete;
};

struct Locale::_Body {
	Opt<Locale const> parent;
	std::string name;
	StrMap<Thm const> thms;
	StrMap<Locale const> locales;
	Map<size_t,std::string> assm_names;
	std::multimap<std::string,Import,std::less<>> imports;
	_Body() {}
	_Body( Opt<Locale const> parent, std::string_view const& name ) : parent(parent), name(name) {}
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
		Intp(src,tgt), _src(src), _tgt(tgt) {
	}
	Locale const& source() const& {
		return _src;
	}
	Locale& target() & {
		return _tgt;
	}
	/** automatic instantiation */
	bool instantiates( bool mod = false ) {
		if( auto v = fixing() ) {
			if( auto t = _tgt.constant(*v) ) {
				instantiate(*t);
			} else if( mod ) {
				instantiate( _tgt.fix(*v) );
			} else {
				throw Error("\"instantiation must be specified\"")(*v);
			}
			return true;
		}
		return false;
	}
	Opt<std::pair<std::string, CTerm>> assuming() & {
		if( auto const& assm = Intp::assuming() ) {
			if( auto const& name = _src.find_assm_name(revision()) ) {
				return std::pair{*name,*assm};
			}
			throw Error("\"unnamed assumption\"")(*assm);
		}
		return {};
	}
	void discharge( Thm const& thm ) {
		Intp::discharge(thm);
	}
	/** automatically discharge assumption */
	bool discharges( bool mod = false ) {
		auto x = assuming();
		if( !x ) {
			return false;
		}
		auto [name,assm] = *x;
		// if this assumption is already discharged, then reuse it
		if( auto opt = _tgt.find_thm(name,[&](Thm const& thm){ return assm == thm; },true,true) ) {
			Intp::discharge(*opt);
			return true;
		} else if( mod ) { // if modification is allowed, then make new assumption
			auto thm = _tgt.assume(name,assm);
			Intp::discharge(thm);
			return true;
		} else {
			throw Error("\"failed know\"")(name)(assm);
		}

	}
	void discharge() & {
		if( !discharges() ) {
			throw Error("\"unexpected know\"");
		}
	}
	struct ObtainInfo {
		std::string spec_name;
		std::string sym;
		Thm ex;
		Thm spec;
	};
	Opt<ObtainInfo> obtaining() & {
		if( auto o = Intp::obtaining() ) {
			auto [sym,ex,spec] = *o;
			auto name = _src.find_assm_name(revision());
			if( !name ) {
				throw Error("\"unnamed obtain\"")(sym)(spec);
			}
			return ObtainInfo{*name,sym,ex,spec};
		}
		return {};
	}
	/** retain constant by specification */
	void retain( CTerm c, Thm const& thm ) &;
	/** retain constant by knowledge */
	void retain( CTerm c );
	/** automatic retain */
	bool retains();
	/** @brief Obtains a theorem in the interpretation. */
	Opt<Thm> find_thm(
		std::string_view const& name,
		Opt<std::function<bool(Thm const&)> const&> test,
		bool noprefix
	) const;
};

inline Locale::Locale() : _ref(Ref<_Body>::make()) {};
inline Locale Locale::branch() const {
	return Locale(Ref<_Body>::make(Opt<Locale const>(*this),""), Ctxt::branch());
}
inline Locale Locale::branch( std::string_view const& name ) {
	auto const& loc = Locale(Ref<_Body>::make(Opt<Locale const>(*this),name), Ctxt::branch());
	_ref->locales.emplace(name,loc);
	return loc;
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

inline Opt<std::string> Locale::find_assm_name( size_t rev ) const {
	if( auto x = _ref->assm_names.finds(rev) ) {
		return x->second;
	}
	return {};
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