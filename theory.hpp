#ifndef _THEORY_HPP
#define _THEORY_HPP
#include<filesystem>
#include"map.hpp"
#include"rewrite.hpp"
#include"elim.hpp"

class AThm;
class Import;
using ThmInfo = Sum<void*,Intro,Elim,Rewrite::Rule,Rewrite::ImpInfo>;

template<typename T>
using StrMMap = MMap<std::string,T>;

inline std::string make_spec_name( std::string base ) {
	return std::move(base)+"#spec";
}

extern std::string const NONREC_IMPORT;
extern std::string const ANONYM_THY;

struct Thy : public Ctxt {
	using Thms = StrMMap<Pair<Thm,ThmInfo>>;
	using ThmTest = std::function<Opt<Thm>( Import const&, std::string_view const& name, Thm const&, ThmInfo const& )>;
private:
	struct _Body;
	Ref<_Body> _ref;
	Thy( Ref<_Body> const& ref, Ctxt const& ctxt ) : _ref(ref), Ctxt(ctxt) {}
	static ThmTest const _triv_test;
	/** Finds theorem by path */
	Opt<Thm> _find_thm(
		std::string_view const& path,
		Import const& import,
		ThmTest const& test,
		bool allow_ancestor,
		bool allow_rec
	) const;
	/** @brief Finds theorem with prefix */
	Opt<Thm> _find_thm(
		std::string_view const& pre,
		std::string_view const& rest,
		Import const& import,
		ThmTest const& test,
		bool allow_ancestor,
		bool allow_rec
	) const;
	/** Finds theorem by unprefixed name */
	Opt<Thm> _find_thm_name(
		std::string_view const& name,
		Import const& import,
		ThmTest const& test,
		bool allow_ancestor,
		bool allow_rec
	) const;
	/** Finds theorem from local theorems */
	Opt<Thm> _find_thm_local(
		std::string_view const& name,
		Import const& import,
		ThmTest const& test
	) const;
	/** Finds theorem by unprefixed name */
	Opt<Thm> _find_thm_unqualified(
		std::string_view const& name,
		Import const& import,
		ThmTest const& test,
		bool allow_ancestor,
		bool allow_rec
	) const;
	/** Finds term property */
	Opt<Pair<Thm,ThmInfo>> _find_term_thm(
		Term const& t,
		std::string const& prop,
		Import const& import,
		bool allow_rec
	) &;
	/** Finds theory by path */
	Opt<Import> _find_thy(
		std::string_view const& path,
		std::function<void(Thy&,std::istream&,std::string_view const&)> const& reader,
		std::function<bool(Thy const&)> const& test,
		bool allow_ancestor,
		bool allow_nonrec
	);
	/** Finds theory with prefix */
	Opt<Import> _find_thy(
		std::string_view const& pre,
		std::string_view const& rest,
		std::function<void(Thy&,std::istream&,std::string_view const&)> const& reader,
		std::function<bool(Thy const&)> const& test,
		bool allow_ancestor,
		bool allow_nonrec
	) &;
	Opt<Import> _find_thy_name(
		std::string_view const& name,
		std::function<void(Thy&,std::istream&,std::string_view const&)> const& reader,
		std::function<bool(Thy const&)> const& test,
		bool allow_ancestor,
		bool allow_nonrec
	);
	Thy _branch( std::string_view const& name, std::filesystem::path const& dir, bool is_scope, Intp const& intp ) const&;
	Import& _add_import( Import const& im, bool prior ) &;
	friend Import;
public:
	struct Error : public ::Error {
		static inline Term const RT = "#thy";
		Error(Term const& term) : ::Error(RT(term)) {}
	};
	/** construct a root theory */
	Thy( std::string_view const& name, std::filesystem::path const& dirname );
	/** @brief Creates an anonymous branch theory.
	 */
	Thy branch() const&;
	/** Creates a named branch. */
	Thy branch( std::string_view const& name, std::filesystem::path const& dir );
	/** Creates a namespace. */
	Thy scope( std::string_view const& name );
	Thy scope_temp( std::string_view const& name ) const;
	std::string const& name() const &;
	auto name() && = delete;
	std::string path() const&;
	/** Self import */
	Import self() const &;
	/** Import from the parent. */
	Opt<Import&> parent() &;
	Opt<Import const&> parent() const &;
	/** The directory name for the theory. */
	std::filesystem::path const& dir() const&;
	auto dir() && = delete;
	/** @brief Finds a named theorem from the theory or an ancestor. */
	Opt<Thm> find_thm(
		std::string_view const& path,
		ThmTest const& test = _triv_test
	) const;
	/** @brief Obtains a named theorem from the theory.
	 */
	Thm thm(std::string_view const& name) const;
	/** @brief Adds a named theorem in the theory.
	 * @exception is thrown if the theorem doesn't belong to this theory
	 */
	void add_thm(std::string_view const& name, Thm const& thm, ThmInfo const& info = {}) &;
	/** Finds a term property */
	Opt<Pair<Thm,ThmInfo> const&> find_term_thm( Term const& t, std::string const& prop ) &;
	/** Gets a term property */
	Pair<Thm,ThmInfo> const& term_thm( Term const& t, std::string const& prop ) & {
		return find_term_thm(t,prop).value_or_throw( Error("\"missing term property\"")(prop)(t) );
	}
	/** @brief Assigns a theorem as a term property. */
	void add_term_thm( Term const& t, std::string const& prop, Thm const& thm, ThmInfo const& info = {} ) &;
	/** Finds the name of assumption made in the revision */
	Opt<std::string> find_assm_name( size_t rev ) const;
	/** Assuming a closed term. */
	Thm add_assm(std::string_view const& name, CTerm const& assm);
	Pair<CTerm,Thm> obtain( std::string_view const& sym, Thm const& ex, std::string_view const& spec_name, bool declare );
	/** Gives interpretation for an ancestor context. */
	Intp interpret_ancestor( Ctxt const& ctxt ) const &;
	bool has_ancestor( Ctxt const& ctxt ) const &;
	/** Before making an import, check it is not recursive */
	void check_loop_import( Thy const& origin, bool rec ) const;
	/** Adds an import. */
	Import& add_import( std::string_view const& prefix, Import const& im, bool rec, bool override ) &;
	/** Remove import */
	void erase_import( std::string_view const& prefix ) &;
	/** multimap of qualified imports */
	StrMMap<Pair<Import,bool>> const& imports() const;
	/** @brief Finds a theory.
	 * @return initial import of the theory into this theory.
	 */
	Opt<Import> find_thy(
		std::string_view const& path,
		std::function<void(Thy&,std::istream&,std::string_view const&)> const& reader,
		std::function<bool(Thy const&)> const& test = []( Thy const& ){ return true; }
	);
	Import thy(
		std::string_view const& name,
		std::function<void(Thy&,std::istream&,std::string_view const&)> reader,
		std::function<bool(Thy const&)> const& test = []( Thy const& ){ return true; }
	);
	Syntax& modify_syntax() &;
	Syntax const& syntax() const&;
	auto pretty_sym( std::string_view const& s ) const& {
		return syntax().pretty_sym(s);
	}
	auto pretty( Term const& t ) const& {
		return syntax().pretty(t);
	}
	auto pretty( CTerm const& t ) const& {
		return syntax().pretty(t);
	}
	auto pretty( Thm const& t ) const& {
		return syntax().pretty(t);
	}
	auto pretty( Rewrite::Rule const& rule ) const& {
		return [&]( std::ostream& os )->std::ostream&{
			return os << '#' << (rule.cong ? "cong" : "simp" ) << ": " << pretty((Thm const&)rule);
		};
	}
	auto pretty_ctxt() const& {
		return syntax().pretty_ctxt(*this);
	}
	auto pretty( Subst const& subst ) const& {
		return syntax().pretty_subst(*this);
	}
	Opt<Rewrite&> find_rewriter( std::string_view const& rew_name ) && = delete;
	Opt<Rewrite const&> find_rewriter( std::string_view const& rew_name ) const &;
	Rewrite const& rewriter( std::string_view const& rew_name ) const & {
		auto o = find_rewriter(rew_name);
		if( !o ) throw Error("\"rewriter not found\"")(rew_name);
		return *o;
	}
	Rewrite& modify_rewriter( std::string_view const& rew_name ) &;
	void reset_rewrite() &;
	void register_refl( Thm const& thm ) &;
	void register_imp( Thm const& thm, bool dir ) &;
	void register_trans( Thm const& thm ) &;
	Thm trans( Term const& rel1, Term const& rel3 ) &;
	void register_dual( Thm const& thm ) &;
	Thm dualize( Thm const& thm, Resolver& resolver ) &;
	void import_rewrite( Import const& import, bool override_default ) &;
	Resolver resolver( char log = 0 ) const &;
	Thm prove( CTerm const& claim, char log = 0 ) const &;
	Pair<std::string,Thm> define( Term const& eq, Opt<std::string const&> name ) &;
	/** Pretty printer for the theory */
	std::ostream& pretty(
		std::ostream& os,
		std::function<std::ostream&(std::ostream&)> const& endl,
		bool thms,
		unsigned short indent,
		bool scope,
		bool path,
		bool print_rewrite
	) const &;
	auto const pretty(
		std::function<std::ostream&(std::ostream&)> const& endl = ENDL,
		bool thms = true,
		unsigned short indent = 0,
		bool scope = false,
		bool path = true,
		bool print_rewrite = false
	) const & {
		return [&endl,thms,indent,scope,path,print_rewrite,this]( std::ostream& os )->std::ostream&{
			return pretty(os,endl,thms,indent,scope,path,print_rewrite);
		};
	}
	/** Pretty printer for rewriter */
	std::ostream& pretty_rewrite(
		std::ostream& os,
		Rewrite const& rew,
		size_t n,
		std::function<std::ostream&(std::ostream&)> const& prefix,
		std::function<std::ostream&(std::ostream&)> const& endl
	) const &;
	auto pretty_rewrite(
		Rewrite const& rew,
		size_t n,
		std::function<std::ostream&(std::ostream&)> const& prefix,
		std::function<std::ostream&(std::ostream&)> const& endl
	) const & {
		return [&rew,n,&prefix,&endl,this]( std::ostream& os )->std::ostream&{
			return pretty_rewrite(os,rew,n,prefix,endl);
		};
	}

	std::function<std::ostream&(std::ostream&)> print_path( bool path = true ) const&;
	std::function<std::ostream&(std::ostream&)> print_thms( std::string_view const& name, std::string_view const& prefix = "\t" ) const&;
	friend bool operator==( Thy const& x, Thy const& y );
};
inline bool operator==( Thy const& x, Thy const& y ) {
	return x._ref.eq_ref(y._ref);// theories are equal if they refer to the same body
}

class Import : public Intp {
	friend Thy;
	Thy mutable _src;//
	/** creates import
	 * @param src the theory to be interpreted
	 * @param tgt the theory that interprets src
	 */
	Import( Intp const& intp, Thy const& src ) : Intp(intp), _src(src) {}
public:
	/** @brief Import a child theory into the parent.
	 */
	static Import make( Thy const& src, Thy const& tgt ) {
		if( (Ctxt const&)src == tgt ) {// just a namespace
			return Import(src.self(),src);
		}
		return Import(Intp::make(src,tgt),src);
	}
	Thy& source() const & {
		return _src;
	}
	Thy source() && {
		return std::move(_src);
	}
	/** @brief Composition of imports.
	 * The argument should import this target.
	 */
	Import compose( Import const& other ) const & {
		return Import(Intp::compose(other),_src);
	}
	Opt<Pair<CTerm,std::string>> assuming() const & {
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
	Sum<Fix,Assume,Obtain,std::nullptr_t> modification( size_t i ) const& {
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
	std::function<std::ostream&(std::ostream&)> pretty(
		std::function<std::ostream&(std::ostream&)> const& endl = ENDL,
		size_t indent = 0
	) const &;
};

/** Annotated theorem */
class AThm : public Thm {
	friend Thy;
	friend Import;
public:
	AThm( Thm const& thm, ThmInfo const& info = {} ) : Thm(thm), info(info) {}
	ThmInfo info;
};

inline Import Thy::self() const& {
	return Import(Ctxt::self(),*this);
}
inline Import Thy::thy(
	std::string_view const& name,
	std::function<void(Thy&,std::istream&,std::string_view const&)> reader,
	std::function<bool(Thy const&)> const& test
) {
	auto ret = find_thy(name,reader,test);
	if( !ret ) throw Error("\"theory not found\"")(name);
	return *ret;
}

auto operator<<(std::ostream& os, Thy && loc) = delete;
inline std::ostream& operator<<( std::ostream& os, Thy const& loc ) {
	return os << loc.pretty([]( std::ostream& os )->std::ostream&{ return os << std::endl; });
}

#endif