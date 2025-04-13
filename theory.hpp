#ifndef _THEORY_HPP
#define _THEORY_HPP
#include<map>
#include"util.hpp"
#include"syntax.hpp"

class Rewriter;

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

class Thy : public Ctxt {
	using Thms = std::multimap<std::string,std::pair<Thm,ThmInfo>,std::less<>>;
	struct _Body;
	Ref<_Body> _ref;
	Thy( Ref<_Body> const& ref, Ctxt const& ctxt ) : _ref(ref), Ctxt(ctxt) {
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
		Thy const& orig
	) const;
	/** @brief Finds a named theorem with prefix from the theory or an ancestor. */
	Opt<AThm> _find_thm(
		std::string_view const& pre,
		std::string_view const& name,
		std::function<Thm(Thm const&)> const& preproc,
		std::function<bool(AThm const&)> const& test,
		Thy const& orig
	) const;
	friend Import;
public:
	struct Error : public ::Error {
		Error(Term const& term) : ::Error(term) {}
	};
	static Error const ThyNotFound;
	struct TheoremNotFound : public Error {
		TheoremNotFound(std::string_view const& name) :
			Error(Term("#theorem_not_found")(name)) {}
	};
	Thy( std::string_view const& name, std::string_view const& dirname );
	/** make context as theory */
	Thy( Thy const& parent, Ctxt const& ctxt, std::string_view const& name, std::string_view const& dirname );
	/** Creates an anonymous branch theory. */
	Thy branch() const;
	/** Creates a named branch. */
	Thy branch( std::string_view const& name, std::string_view const& dirname );
	std::string const& name() const &;
	auto name() && = delete;
	/** Obtains the parent theory. */
	Opt<Thy const&> parent() const &;
	Opt<Thy&> parent() &;
	/** The directory name for the theory. */
	std::string const& dir() const&;
	auto dir() && = delete;
	/** @brief Finds a named theorem from the theory or an ancestor. */
	Opt<AThm> find_thm(
		std::string_view const& name,
		std::function<bool(AThm const&)> const& test = _triv_test,
		bool ancestor = true,
		bool noprefix = false
	) const;
	/** @brief Obtains a named theorem from the theory.
	 * @exception TheoremNotFound is thrown if the name doesn't match any.
	 */
	AThm thm(std::string_view const& name) const;
	/** @brief Adds a named theorem in the theory.
	 * @exception is thrown if the theorem doesn't belong to this theory
	 */
	AThm add_thm(std::string_view const& name, Thm const& thm, ThmInfo const& info = {});
	/** finds the name of assumption made in the revision */
	Opt<std::string> find_assm_name( size_t rev ) const;
	/** Assuming a closed term. */
	Thm add_assm(std::string_view const& name, CTerm const& assm);
	std::pair<CTerm,Thm> obtain( std::string_view const& sym, Thm const& ex, std::string_view const& spec_name );
	/** Declares import */
	Import& import(std::string_view const& name, Thy const& loc) &;
	/** multimap of imports */
	StrMMap<Import> const& imports() const;
	/** Finds branch theory */
	Opt<Thy> find_thy(std::string_view const& name, bool ancestor = true) const;
	Thy thy(std::string_view const& name) const {
		if( auto x = find_thy(name) ) {
			return *x;
		}
		throw Error("\"not found\"")(name);
	}
	Rewriter& rewriter() &;
	Rewriter const& rewriter() const &;
	Rewriter rewriter() && = delete;
	void setup_definer( Thm const& beta ) &;
	std::pair<std::string,Thm> define( Term const& fxs, Term const& r, Opt<std::string const&> name) &;
	/** Pretty printer for context */
	std::function<std::ostream&(std::ostream&)> const pretty(Syntax const& syntax, size_t indent = 0) const &;
	std::function<std::ostream&(std::ostream&)> const pretty(Syntax&&,size_t) = delete;
	std::function<std::ostream&(std::ostream&)> const print_name(Syntax const& syntax) const&;
	std::function<std::ostream&(std::ostream&)> const print_name(Syntax&&) = delete;
	std::function<std::ostream&(std::ostream&)> print_thms( std::string_view const& name, Syntax const& syntax = SYNTAX, std::string_view const& prefix = "\t" ) const&;
};

/** Annotated theorem */
class AThm : public Thm {
	Thy _thy;
	AThm( Thy const& thy, Thm const& thm, ThmInfo const& info = {} ) : _thy(thy), Thm(thm), info(info) {}
	friend Thy;
	friend Import;
public:
	ThmInfo info;
	AThm weaken( Thy const& thy ) const {
		return AThm(thy,Thm::weaken(thy),info);
	}
};

class Import : public Intp {
	Thy const _src;
	Thy _tgt;
	/** @brief Obtains a theorem in the interpretation. */
	Opt<AThm> _find_thm(
		std::string_view const& name,
		std::function<Thm(Thm const&)> const& preproc,
		std::function<bool(AThm const&)> const& test,
		bool noprefix,
		Thy const& orig
	) const;
	friend Thy;
public:
	/** creates import
	 * @param src the theory to be interpreted
	 * @param tgt the theory that interprets src
	 */
	Import( Thy const& tgt, Thy const& src ) :
		Intp(src,tgt), _src(src), _tgt(tgt) {
	}
	Thy const& source() const& {
		return _src;
	}
	Thy& target() & {
		return _tgt;
	}
	Thy const& target() const & {
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
	/** Pretty printer for import */
	std::function<std::ostream&(std::ostream&)> const pretty(Syntax const& syntax, size_t indent = 0) const &;
	std::function<std::ostream&(std::ostream&)> const pretty(Syntax&&,size_t) = delete;
};

inline std::ostream& operator<<(std::ostream& os, Thy const& loc) {
	return os << loc.pretty(SYNTAX);
}

Opt<Thm> proves( CTerm const& claim, Thy const& thy );
Thm prove( CTerm const& claim, Thy const& thy );

#endif