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
struct RewriteRule {
	CTerm pat;
	Thm thm;
};
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
		std::function<bool(AThm const&)> const& test,
		Import const& import
	) const;
	/** @brief Finds a named theorem with prefix from the theory or an ancestor. */
	Opt<AThm> _find_thm(
		std::string_view const& pre,
		std::string_view const& name,
		std::function<bool(AThm const&)> const& test,
		Import const& import
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
	/** @brief Creates an anonymous branch theory.
	 * @return Import from parent into the child.
	 */
	Import const& branch() const;
	/** Creates a named branch. */
	Import const& branch( std::string_view const& name, std::string_view const& dirname );
	/** Creates a namespace. */
	Thy scope( std::string_view const& name ) const;
	std::string const& name() const &;
	auto name() && = delete;
	/** Self import */
	Import self() const &;
	/** Import from the parent. */
	Opt<Import const&> parent() const &;
	/** The directory name for the theory. */
	std::string const& dir() const&;
	auto dir() && = delete;
	/** @brief Finds a named theorem from the theory or an ancestor. */
	Opt<AThm> find_thm(
		std::string_view const& name,
		std::function<bool(AThm const&)> const& test = _triv_test
	) const;
	/** @brief Obtains a named theorem from the theory.
	 * @exception TheoremNotFound is thrown if the name doesn't match any.
	 */
	AThm thm(std::string_view const& name) const;
	/** @brief Adds a named theorem in the theory.
	 * @exception is thrown if the theorem doesn't belong to this theory
	 */
	AThm add_thm(std::string_view const& name, Thm const& thm, ThmInfo const& info = {});
	/** Finds the name of assumption made in the revision */
	Opt<std::string> find_assm_name( size_t rev ) const;
	/** Assuming a closed term. */
	Thm add_assm(std::string_view const& name, CTerm const& assm);
	std::pair<CTerm,Thm> obtain( std::string_view const& sym, Thm const& ex, std::string_view const& spec_name );
	/** Gives interpretation for an ancestor context. */
	Intp interpret_ancestor( Ctxt const& ctxt ) const &;
	/** Weaken theorem from an ancestor. */
	Thm weaken( Thm const& thm ) const;
	/** Weaken closed term from an ancestor. */
	CTerm weaken( CTerm const& t ) const;
	/** Adds an import. */
	Import& add_import( std::string_view const& name, Import const& im ) &;
	/** multimap of imports */
	StrMMap<Import> const& imports() const;
	/** @brief Finds a theory.
	 * @return initial import of the theory into this theory.
	 */
	Opt<Import> find_thy( std::string_view const& name, std::function<void(Thy&,Parser&)> reader );
	Import thy( std::string_view const& name, std::function<void(Thy&,Parser&)> reader );
	Syntax& syntax() &;
	Syntax const& syntax() const&;
	auto pretty( Term const& t ) const {
		return syntax().pretty(t);
	}
	auto pretty( CTerm const& t ) const {
		return syntax().pretty(t);
	}
	auto pretty( Thm const& t ) const {
		return syntax().pretty(t);
	}
	Rewriter& rewriter() &;
	Rewriter const& rewriter() const &;
	Rewriter rewriter() && = delete;
	Thm rewrite( Thm const& thm ) const&;
	void setup_definer( Thm const& beta ) &;
	std::pair<std::string,Thm> define( Term const& fxs, Term const& r, Opt<std::string const&> name) &;
	/** Pretty printer for the theory */
	std::function<std::ostream&(std::ostream&)> const pretty( size_t indent = 0 ) const &;
	std::function<std::ostream&(std::ostream&)> const print_name() const&;
	std::function<std::ostream&(std::ostream&)> print_thms( std::string_view const& name, std::string_view const& prefix = "\t" ) const&;
};

class Import : public Intp {
	friend Thy;
	Thy mutable _src;//
	Thy mutable _tgt;
	/** creates import
	 * @param src the theory to be interpreted
	 * @param tgt the theory that interprets src
	 */
	Import( Intp const& intp, Thy const& tgt, Thy const& src ) :
		Intp(intp), _src(src), _tgt(tgt) {
	}
public:
	Thy& source() const & {
		return _src;
	}
	Thy source() && = delete;
	Thy& thy() const & {
		return _tgt;
	}
	Thy thy() && {
		return _tgt;
	}
	/** @brief Imports a child theory of the source.
	 */
	Import import( Thy const& other ) const & {
		return Import(this->interpret(other),_tgt,other);
	}
	/** @brief Composition of imports.
	 * The argument should import this target.
	 */
	Import compose( Import const& other ) const & {
		if( _tgt != other._src ) throw Error("\"wrong compose\"");
		return Import(Intp::compose(other),other._tgt,_src);
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
	/** Pretty printer for import */
	std::function<std::ostream&(std::ostream&)> const pretty( size_t indent = 0 ) const &;
};

/** Annotated theorem */
class AThm : public Thm {
	Import _import;
	AThm( Import const& import, Thm const& thm, ThmInfo const& info = {} ) : _import(import), Thm(thm), info(info) {}
	friend Thy;
	friend Import;
public:
	ThmInfo info;
};

Opt<Thm> proves( CTerm const& claim, Thy const& thy );
Thm prove( CTerm const& claim, Thy const& thy );

inline Import Thy::self() const& {
	return Import(Ctxt::self(),*this,*this);
}
inline Import Thy::thy( std::string_view const& name, std::function<void(Thy&,Parser&)> reader ) {
	auto ret = find_thy(name,reader);
	if( !ret ) throw Error("\"theory not found\"");
	return *ret;
}

inline std::ostream& operator<<(std::ostream& os, Thy const& loc) {
	return os << loc.pretty();
}
inline std::ostream& operator<<( std::ostream& os, RewriteRule const& rule ) {
	return os << '[' << rule.pat << "] " << rule.thm;
}

#endif