#ifndef _syntax_hpp
#define _syntax_hpp

#include<iostream>
#include"core.hpp"
#include"lexer.hpp"

template<class I, class T>
void out_sep(
	std::ostream& os, I it, I const& end, std::string const& sep,
	std::function<void(std::ostream&,T const&)> const& elm =
		[](std::ostream& os, T const& e){os << e;}
) {
	if( it != end ) {
		elm(os,*it);
		it++;
		while( it != end ) {
			os << sep;
			elm(os,*it);
			it++;
		}
	}
}

inline std::ostream& operator<<(
	std::ostream& stream, 
	std::function<std::ostream& (std::ostream&)> const& manipulator
) {
    return manipulator( stream );
}

class Parser;

class Syntax {
public:
	struct Prefix {
		int llevel;
		int rlevel;
	};
	struct Infix {
		int level;
		int llevel;
		int rlevel;
	};
	struct Binder {
		int llevel;
		int rlevel;
		StrMap<std::string> bbinds;// ∀x ∈ X. _
		StrMap<std::string> mid_of;// bbind -> "∈"
	};
	struct Opener {
		std::string closer;
		Opt<std::string> empty;// {}
		Opt<std::string> singleton;// {_}
		Opt<std::string> compr;// {x. _}
		StrMap<std::string> bcompr;// {x ∈ X. _}
		StrMap<std::string> mid_of;// bcompr -> "∈"
	};
private:
	StrMap<Opener> _openers;
	StrSet _closers;
	StrMap<Prefix> _prefixes;
	StrMap<Infix> _infixes;
	StrMap<Binder> _binders;
	StrMap<std::string> _binder_of;// bbind → "λ"
	StrMap<std::string> _opener_of;// bcompr → "{"
	bool _print_ctxt = false;
public:
	Syntax();
	bool prints_ctxt() const {
		return _print_ctxt;
	}
	void print_ctxt( bool b ) {
		_print_ctxt = b;
	}
	void prefix(std::string const& sym, int level, int rlevel) {
		_prefixes.insert({sym,{level,rlevel}});
	}
	Opt<std::pair<std::string const,Prefix> const&> finds_prefix(std::string_view const& sym) const {
		return _prefixes.finds(sym);
	}
	void infix(std::string const& sym, int level, int llevel, int rlevel) {
		_infixes.insert({sym,{level,llevel,rlevel}});
	}
	Opt<std::pair<std::string const,Infix> const&> finds_infix(std::string_view const& sym) const {
		return _infixes.finds(sym);
	}
	bool has_closer(std::string_view const& sym) const {
		return _closers.contains(sym);
	}
	Opt<std::pair<std::string const, Opener> const&> finds_opener( std::string_view const& sym ) const {
		return _openers.finds(sym);
	}
	void binder( std::string_view const& binder, int llevel, int rlevel ) {
		_binders.emplace(binder,Binder{llevel,rlevel,{}});
	}
	auto finds_binder( std::string_view const& binder ) const& {
		return _binders.finds(binder);
	}
	void binder_mid( std::string_view const& prefix, std::string_view const& mid, std::string_view const& actual ) & {
		auto binder = _binders.finds(prefix);
		if( !binder ) throw Error("\"binder not registered\"")(prefix)(mid);
		binder->second.bbinds.emplace(mid,actual);
		binder->second.mid_of.emplace(actual,mid);
		_binder_of.emplace(actual,prefix);
	}
	void empty_compr( std::string_view const& opener, std::string_view const& closer, std::string_view const& actual ) & {
		auto const& [it,fl] = _openers.emplace(opener,std::string(closer));
		it->second.empty.emplace(actual);
		_opener_of.emplace(actual,opener);
		_closers.emplace(closer);
	}
	void singleton_compr( std::string_view const& opener, std::string_view const& closer, std::string_view const& actual ) & {
		auto const& [it,fl] = _openers.emplace(opener,std::string(closer));
		it->second.singleton.emplace(actual);
		_opener_of.emplace(actual,opener);
		_closers.emplace(closer);
	}
	void compr( std::string_view const& opener, std::string_view const& closer, std::string_view const& actual ) & {
		auto const& [it,fl] = _openers.emplace(opener,std::string(closer));
		it->second.compr.emplace(actual);
		_opener_of.emplace(actual,opener);
		_closers.emplace(closer);
	}
	void bcompr( std::string_view const& opener, std::string_view const& mid, std::string_view const& closer, std::string_view const& actual ) & {
		auto const& [it,fl] = _openers.emplace(opener,std::string(closer));
		it->second.bcompr.emplace(mid,actual);
		it->second.mid_of.emplace(actual,mid);
		_opener_of.emplace(actual,opener);
		_closers.emplace(closer);
	}
	std::ostream& pretty_sym( std::ostream& os, std::string_view const& sym ) const &;
	std::function<std::ostream&(std::ostream&)> pretty_sym( std::string_view const& sym ) const & {
		return [this,sym](std::ostream& os) -> std::ostream& {
			return pretty_sym(os,sym);
		};
	}
	std::ostream& pretty( std::ostream& os, Term const& term, int level = 0 ) const &;
	std::function<std::ostream&(std::ostream&)> pretty(Term const& term, int level = 0) const & {
		return [this,&term,level](std::ostream& os) -> std::ostream& {
			return pretty(os,term,level);
		};
	}
	std::function<std::ostream&(std::ostream&)> pretty_thms(StrMap<Thm> const& thms) const &;
	std::ostream& pretty_ctxt( std::ostream& os, Ctxt const& ctxt, size_t rev ) const &;
	std::function<std::ostream&(std::ostream&)> pretty_ctxt(Ctxt const& ctxt) const & {
		return [this,ctxt]( std::ostream& os )->std::ostream& {
			return pretty_ctxt(os,ctxt,ctxt.revision());
		};
	}
	std::function<std::ostream&(std::ostream&)> pretty_subst(Subst const& subst) const &;
};

extern Syntax SYNTAX;

inline std::ostream& operator<<(std::ostream& os, Term const& t) {
	return os << SYNTAX.pretty(t,0);
}

inline std::ostream& operator<<(std::ostream& os, CTerm const& t) {
	return os << SYNTAX.pretty(t,0) << " @" << t.ctxt().id();
}

inline std::ostream& operator<<(std::ostream& os, Subst const& subst) {
	return os << SYNTAX.pretty_subst(subst);
}

inline std::ostream& operator<<(std::ostream& os, Ctxt const& ctxt) {
	return os << SYNTAX.pretty_ctxt(ctxt);
}

#endif