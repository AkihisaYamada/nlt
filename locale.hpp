#ifndef _LOCALE_HPP
#define _LOCALE_HPP
#include<map>
#include"util.hpp"
#include"syntax.hpp"

class Locale;
struct ThmInfo {
	Opt<Intro> intro;
	Opt<Elim> elim;
};
class AThm;
class Import;
template<typename T>
using StrMMap = std::multimap<std::string,T,std::less<>>;

inline std::string make_spec_name( std::string base ) {
	return std::move(base)+"#spec";
}

class Locale : public Ctxt {
	using Thms = std::multimap<std::string,std::pair<Thm,ThmInfo>,std::less<>>;
	struct _Body;
	Ref<_Body> _ref;
	Locale( Ref<_Body> const& ref, Ctxt const& ctxt ) : _ref(ref), Ctxt(ctxt) {
		assert( !parent() || *parent() == ctxt.parent() );
	}
	static std::function<Thm(Thm const&)> const _triv_proc;
	static std::function<bool(AThm const&)> const _triv_test;
	Opt<AThm> _find_thm(
		std::string_view const& name,
		std::function<Thm(Thm const&)> const& proc/* modifies the found theorem, weakening or instantiation */,
		std::function<bool(AThm const&)> const& test,
		bool ancestor,
		bool noprefix,
		Locale const& orig
	) const;
	/** @brief Finds a named theorem with prefix from the locale or an ancestor. */
	Opt<AThm> _find_thm(
		std::string_view const& pre,
		std::string_view const& name,
		std::function<Thm(Thm const&)> const& preproc,
		std::function<bool(AThm const&)> const& test,
		Locale const& orig
	) const;
	friend Import;
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
	/** make context as locale */
	Locale( Locale const& loc, Ctxt const& ctxt );
	/** Creates an anonymous branch locale. */
	Locale branch() const;
	/** Creates a named branch. */
	Locale branch(std::string_view const& name);
	/** Obtains the parent locale. */
	Opt<Locale const> parent() const;
	/** @brief Finds a named theorem from the locale or an ancestor. */
	Opt<AThm> find_thm(
		std::string_view const& name,
		std::function<bool(AThm const&)> const& test = _triv_test,
		bool ancestor = true,
		bool noprefix = false
	) const;
	/** @brief Obtains a named theorem from the locale.
	 * @exception TheoremNotFound is thrown if the name doesn't match any.
	 */
	AThm thm(std::string_view const& name) const;
	/** @brief Adds a named theorem in the locale.
	 * @exception is thrown if the theorem doesn't belong to this locale
	 */
	AThm add_thm(std::string_view const& name, Thm const& thm, ThmInfo const& info = {});
	/** finds the name of assumption made in the revision */
	Opt<std::string> find_assm_name( size_t rev ) const;
	/** Assuming a closed term. */
	Thm add_assm(std::string_view const& name, CTerm const& assm);
	std::pair<CTerm,Thm> obtain( std::string_view const& sym, Thm const& ex, std::string_view const& spec_name );
	/** Declares import */
	Import& import(std::string_view const& name, Locale const& loc) &;
	/** multimap of imports */
	StrMMap<Import> const& imports() const;
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
	std::function<std::ostream&(std::ostream&)> print_thms( std::string_view const& name, Syntax const& syntax = SYNTAX, std::string_view const& prefix = "\t" ) const&;
};

/** Annotated theorem */
class AThm : public Thm {
	Locale _locale;
	AThm( Locale const& loc, Thm const& thm, ThmInfo const& info = {} ) : _locale(loc), Thm(thm), info(info) {}
	friend Locale;
	friend Import;
public:
	ThmInfo info;
	AThm weaken( Locale const& loc ) const {
		return AThm(loc,Thm::weaken(loc),info);
	}
};
struct Locale::_Body {
	Opt<Locale const> parent;
	std::string name;
	StrMMap<std::pair<Thm,ThmInfo>> thms;
	std::set<Thm> forced_intros;
	StrMap<Locale const> locales;
	Map<size_t,std::string> assm_names;
	std::multimap<std::string,Import,std::less<>> imports;
	_Body() {}
	_Body( Opt<Locale const> parent, std::string_view const& name ) : parent(parent), name(name) {}
};

class Import : public Intp {
	Locale const _src;
	Locale _tgt;
	/** @brief Obtains a theorem in the interpretation. */
	Opt<AThm> _find_thm(
		std::string_view const& name,
		std::function<Thm(Thm const&)> const& preproc,
		std::function<bool(AThm const&)> const& test,
		bool noprefix,
		Locale const& orig
	) const;
	friend Locale;
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
	bool discharges( bool mod = false );
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
	void retain( CTerm c, Thm const& thm ) & {
		Intp::retain(c,thm);
	}
	/** retain constant by knowledge */
	void retain( CTerm c );
	/** automatic retain */
	bool retains();
	AThm subst( AThm const& thm ) const {
		return AThm(_tgt,Intp::subst(thm));
	}
};

inline Locale::Locale() : _ref(Ref<_Body>::make()) {};

inline Locale::Locale( Locale const& parent, Ctxt const& ctxt ) :
	Ctxt(ctxt), _ref(Ref<_Body>::make(parent,"")) {}

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

inline Opt<AThm> Locale::find_thm(
	std::string_view const& name,
	std::function<bool(AThm const&)> const& test,
	bool ancestor,
	bool noprefix
) const {
	return _find_thm(name,_triv_proc,test,ancestor,noprefix,*this);
}

inline AThm Locale::thm(std::string_view const& name) const {
	if( auto opt = find_thm(name) ) {
		return *opt;
	}
	throw TheoremNotFound(name);
}

inline Opt<std::string> Locale::find_assm_name( size_t rev ) const {
	if( auto x = _ref->assm_names.finds(rev) ) {
		return x->second;
	}
	return {};
}

inline StrMMap<Import> const& Locale::imports() const {
	return _ref->imports;
}

inline std::ostream& operator<<(std::ostream& os, Locale const& loc) {
	return os << loc.pretty(SYNTAX);
}

inline Import& Locale::import(std::string_view const& name, Locale const& loc) & {
	auto it = _ref->imports.emplace(std::piecewise_construct,
		std::make_tuple(name),
		std::forward_as_tuple(*this,loc)
	);
	return it->second;
};

#endif