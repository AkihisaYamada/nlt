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
	Thy( Ref<_Body> const& ref, Ctxt const& ctxt ) : _ref(ref), Ctxt(ctxt) {}
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
	/** construct a root theory */
	Thy( std::string_view const& name, std::string_view const& dirname );
	/** Creates an anonymous branch theory. */
	Thy branch() const;
	/** Creates a named branch. */
	Thy branch( std::string_view const& name, std::string_view const& dirname );
	/** Creates a namespace. */
	Thy scope( std::string_view const& name ) const;
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
	friend Thy;
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
public:
	/** creates import
	 * @param src the theory to be interpreted
	 * @param tgt the theory that interprets src
	 */
	Import( Thy const& tgt, Thy const& src ) :
		Intp(tgt.interpret(src)), _src(src), _tgt(tgt) {
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
	Opt<std::pair<CTerm,std::string>> assuming() const & {
		if( auto assm = Intp::assuming() ) {
			auto const& name = _src.find_assm_name(revision());
			assert(name);
			return {{*assm,*name}};
		}
		return {};
	}
	Opt<std::tuple<std::string,Thm,CTerm,std::string>> obtaining() const& {
		if( auto obtain = Intp::obtaining() ) {
			auto const& [sym,ex,spec] = *obtain;
			auto name = _src.find_assm_name(revision());
			return {{ sym, ex, spec, name ? *name : "???" }};
		}
		return {};
	}
	struct Fix : std::string {};
	struct Assume {
		std::string name;
		Term assm;
	};
	struct Obtain {
		Opt<std::string> spec_name;
		std::string sym;
		Term ex;
		Term spec;
	};
	Sum<Fix,Assume,Obtain,nullptr_t> modification( size_t i ) const& {
		auto mod = Intp::modification(i);
		if( auto const& fix = mod.ref<Ctxt::Fix>() ) {
			return Fix(*fix);
		}
		if( auto const& assm = mod.ref<Ctxt::Assume>() ) {
			auto name = _src.find_assm_name(revision()+i);
			assert(name);
			return Assume{*name,*assm};
		}
		if( auto const& obtain = mod.ref<Ctxt::Obtain>() ) {
			auto [sym,ex,spec] = *obtain;
			return Obtain{_src.find_assm_name(revision()+i),sym,ex,spec};
		}
		return nullptr;
	};
	void discharge( Thm const& thm ) {
		Intp::discharge(thm);
	}
	/** retain constant by specification */
	void retain( CTerm c, Thm const& thm ) & {
		Intp::retain(c,thm);
	}
	AThm subst( AThm const& thm ) const {
		return AThm(_tgt,Intp::subst(thm));
	}
	/** Pretty printer for import */
	std::function<std::ostream&(std::ostream&)> const pretty(Syntax const& syntax, size_t indent = 0) const &;
	auto pretty(Syntax&&,size_t) = delete;
};

inline std::ostream& operator<<(std::ostream& os, Thy const& loc) {
	return os << loc.pretty(SYNTAX);
}

Opt<Thm> proves( CTerm const& claim, Thy const& thy );
Thm prove( CTerm const& claim, Thy const& thy );

#endif