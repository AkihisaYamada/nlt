#ifndef _syntax_hpp
#define _syntax_hpp

#include<iostream>
#include"core.hpp"
#include"lexer.hpp"

std::function<std::ostream&(std::ostream&)> const ENDL =
	[]( std::ostream& os )->std::ostream&{ return os << std::endl; };

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
		Opt<std::string> cons;// "," if x + y reads +(x,y)
	};
	struct Binder {
		int llevel;
		int rlevel;
		StrMap<std::pair<std::string,Opt<std::string>>> bbinds;// "∈" → ("∀∈", ",")
	};
	struct Opener {
		std::string closer;
		Opt<std::string> empty;// {}
		Opt<std::string> singleton;// {_}
		Opt<std::string> compr;// {_. _}
		StrMap<std::pair<std::string,Opt<std::string>>> bcompr;// "∈" → ("{_∈_._}", ",")
	};
	struct Empty {
		std::string opener, closer;
	};
	struct Singleton {
		std::string opener, closer;
	};
	struct Compr {
		std::string opener, closer;
	};
	struct BinderRel {
		int llevel;
		int rlevel;
		std::string binder, mid;
		Opt<std::string> cons;
	};
	struct ComprRel {
		std::string opener, mid, closer;
		Opt<std::string> cons;
	};
private:
	StrMap<Opener> _openers;
	StrSet _closers;
	StrMap<Prefix> _prefixes;
	StrMap<Infix> _infixes;
	StrMap<Binder> _binders;
	StrMap<Sum<Empty,Singleton,Compr,BinderRel,ComprRel>> _pretty_of;
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
	void infix( std::string const& sym, int level, int llevel, int rlevel, Opt<std::string> const& cons ) {
		_infixes.insert({sym,{level,llevel,rlevel,cons}});
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
	void binder_mid(
		std::string_view const& prefix,
		std::string_view const& mid,
		std::string_view const& actual,
		Opt<std::string> const& cons 
	) & {
		auto x = _binders.finds(prefix);
		if( !x ) throw Error("\"binder not registered\"")(prefix)(mid);
		auto& [sym,binder] = *x;
		binder.bbinds.emplace(mid,std::pair{std::string(actual),cons});
		_pretty_of.emplace(actual,BinderRel{binder.llevel,binder.rlevel,std::string(prefix),std::string(mid),cons});
	}
	void empty_compr( std::string_view const& opener, std::string_view const& closer, std::string_view const& actual ) & {
		auto const& [it,fl] = _openers.emplace(opener,std::string(closer));
		it->second.empty.emplace(actual);
		_pretty_of.emplace(actual,Empty{std::string(opener),std::string(closer)});
		_closers.emplace(closer);
	}
	void singleton_compr( std::string_view const& opener, std::string_view const& closer, std::string_view const& actual ) & {
		auto const& [it,fl] = _openers.emplace(opener,std::string(closer));
		it->second.singleton.emplace(actual);
		_pretty_of.emplace(actual,Singleton{std::string(opener),std::string(closer)});
		_closers.emplace(closer);
	}
	void compr( std::string_view const& opener, std::string_view const& closer, std::string_view const& actual ) & {
		auto const& [it,fl] = _openers.emplace(opener,std::string(closer));
		it->second.compr.emplace(actual);
		_pretty_of.emplace(actual,Compr{std::string(opener),std::string(closer)});
		_closers.emplace(closer);
	}
	void bcompr( std::string_view const& opener, std::string_view const& mid, std::string_view const& closer, std::string_view const& actual, Opt<std::string> const& cons ) & {
		auto const& [it,fl] = _openers.emplace(opener,std::string(closer));
		it->second.bcompr.emplace(mid,std::pair{actual,cons});
		_pretty_of.emplace(actual,ComprRel{std::string(opener),std::string(mid),std::string(closer),cons});
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
	std::function<std::ostream&(std::ostream&)> pretty_thms( StrMap<Thm> const& thms ) const &;
	std::ostream& pretty_ctxt(
		std::ostream& os,
		Ctxt const& ctxt,
		size_t rev,
		std::function<std::ostream&(std::ostream&)> const& endl
	) const &;
	/** CAUTION: do not move around */
	std::function<std::ostream&(std::ostream&)> pretty_ctxt(
		Ctxt const& ctxt,
		std::function<std::ostream&(std::ostream&)> const& endl = ENDL
	) const & {
		return [&]( std::ostream& os )->std::ostream& {
			return pretty_ctxt(os,ctxt,ctxt.revision(),endl);
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