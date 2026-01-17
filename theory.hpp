#ifndef _THEORY_HPP
#define _THEORY_HPP
#include<map>
#include"rewrite.hpp"

class AThm;
class Import;
class Definer;
using ThmInfo = Sum<int,Intro,Elim,Rewrite::Rule>;

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
	static std::function<Opt<Thm>( Import const&, Thm const&, ThmInfo const& )> const _triv_test;
	/** @brief Finds a named theorem with prefix from the theory or an ancestor. */
	Opt<Thm> _find_thm(
		std::string_view const& pre,
		std::string_view const& name,
		Import const& import,
		std::function<Opt<Thm>( Import const&, Thm const&, ThmInfo const& )> const& test
	) const;
	Opt<Import> _find_thy( std::string_view const& thyname, std::function<void(Thy&,std::istream&,std::string_view const&)> reader ) &;
	void _check_loop_import( Thy const& origin ) const;
	Thy _branch( std::string_view const& name, std::string_view const& dir, bool is_scope, Intp const& intp ) const&;
	void _make_own_rewrite()&;
	friend Import;
public:
	struct Error : public ::Error {
		static inline Term const RT = "#thy";
		Error(Term const& term) : ::Error(RT(term)) {}
	};
	/** name for exact concluder */
	static std::string const EXACT;
	/** name for introduction rules */
	static std::string const INTRO;
	/** name for weak introduction rules */
	static std::string const WEAK;
	/** name for schematic concluders */
	static std::string const CONCL;
	/** name for elimination rules */
	static std::string const ELIM;
	/** prefix for rewrite rules */
	static std::string const REWRITE;
	/** name for inflation rules, φ ⟹ ψ */
	static std::string const INF;
	/** construct a root theory */
	Thy( std::string_view const& name, std::string_view const& dirname );
	/** @brief Creates an anonymous branch theory.
	 */
	Thy branch() const&;
	/** Creates a named branch. */
	Thy branch( std::string_view const& name, std::string_view const& dir ) &;
	/** Creates a namespace. */
	Thy scope( std::string_view const& name ) &;
	Thy scope_temp( std::string_view const& name ) const &;
	std::string const& name() const &;
	auto name() && = delete;
	/** Self import */
	Import self() const &;
	/** Import from the parent. */
	Opt<Import&> parent() &;
	Opt<Import const&> parent() const &;
	/** The directory name for the theory. */
	std::string const& dir() const&;
	auto dir() && = delete;
	/** @brief Finds a named theorem from the theory or an ancestor. */
	Opt<Thm> find_thm(
		std::string_view const& name,
		std::function<Opt<Thm>(Import const&, Thm const&, ThmInfo const&)> const& test = _triv_test
	) const;
	/** @brief Finds a named theorem from the theory or an ancestor, and then interpret.
	 */
	Opt<Thm> find_thm(
		std::string_view const& name,
		Import const& import,
		std::function<Opt<Thm>(Import const&, Thm const&, ThmInfo const&)> const& test = _triv_test,
		bool ancestor = true
	) const;
	/** @brief Obtains a named theorem from the theory.
	 */
	Thm thm(std::string_view const& name) const;
	/** @brief Adds a named theorem in the theory.
	 * @exception is thrown if the theorem doesn't belong to this theory
	 */
	void add_thm(std::string_view const& name, Thm const& thm, ThmInfo const& info = {}) &;
	void add_elim( Thm const& thm ) & {
		add_thm(ELIM,thm,Elim::rule(thm,0,'?'));
	}
	/** Finds the name of assumption made in the revision */
	Opt<std::string> find_assm_name( size_t rev ) const;
	/** Assuming a closed term. */
	Thm add_assm(std::string_view const& name, CTerm const& assm);
	std::pair<CTerm,Thm> obtain( std::string_view const& sym, Thm const& ex, std::string_view const& spec_name, bool declare );
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
	Opt<Import> find_thy( std::string_view const& name, std::function<void(Thy&,std::istream&,std::string_view const&)> reader, bool ancestor = true );
	void add_thy( Thy const& thy ) &;
	Import thy( std::string_view const& name, std::function<void(Thy&,std::istream&,std::string_view const&)> reader );
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
	Opt<Rewrite&> rewriter() && = delete;
	Opt<Rewrite const&> rewriter() const &;
	void reset_rewrite() &;
	Thm dualize( Thm const& thm, Blaster& resolver ) const &;
	void register_refl( Thm const& refl, bool def ) &;
	void register_trans( Thm const& trans ) &;
	void register_dual( Thm const& dual ) &;
	void register_imp( Thm const& imp, bool dir ) &;
	void register_cong( Thm const& cong ) &;
	void register_fallback( Thm const& thm ) &;
	void register_to_true( Thm const thm ) &;
	void add_rewrite_rule( Rewrite::Rules& rules, Thm const& rule, bool cong ) const &;
	void import_rewrite( Thy const& src, Intp const& intp ) &;
	Blaster blaster( char log = 0 ) const &;
	Thm prove( CTerm const& claim, char log = 0 ) const &;
	void setup_definer( Thm const& beta ) &;
	OptRef<Definer>& definer() &;
	std::pair<std::string,Thm> define( Term const& fxs, Term const& r, Opt<std::string const&> name) &;
	/** Pretty printer for the theory */
	std::function<std::ostream&(std::ostream&)> pretty( size_t indent = 0, bool scope = false, bool path = true ) const &;
	std::function<std::ostream&(std::ostream&)> print_name( bool path = true ) const&;
	std::function<std::ostream&(std::ostream&)> print_thms( std::string_view const& name, std::string_view const& prefix = "\t" ) const&;
};

class Import : public Intp {
	friend Thy;
	Thy mutable _src;//
	/** creates import
	 * @param src the theory to be interpreted
	 * @param tgt the theory that interprets src
	 */
	Import( Intp const& intp, Thy const& src ) :
		Intp(intp), _src(src) {
	}
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
	friend Thy;
	friend Import;
public:
	AThm( Thm const& thm, ThmInfo const& info = {} ) : Thm(thm), info(info) {}
	ThmInfo info;
};

inline Import Thy::self() const& {
	return Import(Ctxt::self(),*this);
}
inline Import Thy::thy( std::string_view const& name, std::function<void(Thy&,std::istream&,std::string_view const&)> reader ) {
	auto ret = find_thy(name,reader);
	if( !ret ) throw Error("\"theory not found\"")(name);
	return *ret;
}
inline Opt<Thm> Thy::find_thm(
	std::string_view const& name,
	std::function<Opt<Thm>( Import const&, Thm const&, ThmInfo const& )> const& test
) const {
	return find_thm(name,self(),test);
}
inline std::ostream& operator<<(std::ostream& os, Thy const& loc) {
	return os << loc.pretty();
}

#endif