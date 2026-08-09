#ifndef _syntax_hpp
#define _syntax_hpp

#include<iostream>
#include"core.hpp"

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

struct Syntax {

	struct Prefix {
		int level;
		int rlevel;
		std::string actual;
	};
	struct Postfix {
		int level;
		std::string actual;
	};
	struct Infix {
		int level;
		int llevel;
		int rlevel;
		std::string actual;
		Opt<std::string> cons;// "," if x + y reads +(x,y)
	};
	struct Binder {
		int llevel;
		int rlevel;
		StrMap<std::pair<std::string,Opt<std::string>>> bbinds;// "∈" → ("∀∈", ",")
	};
	struct Opener {
		int level;
		std::string closer;
		Opt<std::string> empty;// {}
		Opt<std::string> singleton;// {_}
		Opt<std::string> compr;// {_. _}
		StrMap<std::pair<std::string,Opt<std::string>>> bcompr;// "∈" → ("{_∈_._}", ",")
	};
	struct Unary {
		bool postfix;
		std::string view;
	};
	struct Binary {
		std::string view;
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
	static int constexpr INVALID = INT_MIN;
	static int constexpr PARSE_ALL = INVALID+1;
	static std::string constexpr BIT0 = "_bit0";
	static std::string constexpr BIT1 = "_bit1";	
private:
	StrMap<Opener> _openers;
	StrMap<Prefix> _prefixes;
	StrMap<Postfix> _postfixes;
	StrMap<Infix> _infixes;
	StrMap<Binder> _binders;
	StrMap<Sum<Unary,Binary,Empty,Singleton,Compr,BinderRel,ComprRel>> _pretty_of;
	bool _print_ctxt = false;
public:
	Syntax();
	bool prints_ctxt() const {
		return _print_ctxt;
	}
	void print_ctxt( bool b ) {
		_print_ctxt = b;
	}
	void prefix( std::string const& view, std::string const& actual, int level, int rlevel ) {
		_prefixes.emplace(view,{level,rlevel,actual});
		_pretty_of.emplace(actual,Unary{false,view});
	}
	Opt<Prefix const&> finds_prefix(std::string_view const& sym) const {
		return _prefixes.finds_value(sym);
	}
	void postfix( std::string const& view, std::string const& actual, int level ) {
		_postfixes.emplace(view,{level,actual});
		_pretty_of.emplace(actual,Unary{true,view});
	}
	Opt<Postfix const&> finds_postfix(std::string_view const& sym) const {
		return _postfixes.finds_value(sym);
	}
	void infix( std::string const& view, std::string const& actual, int level, int llevel, int rlevel, Opt<std::string> const& cons ) {
		_infixes.emplace(view,{level,llevel,rlevel,actual,cons});
		_pretty_of.emplace(actual,Binary{view});
	}
	Opt<Infix const&> finds_infix(std::string_view const& sym) const {
		return _infixes.finds_value(sym);
	}
	Opt<Pair<std::string const&, Opener const&>> finds_opener( std::string_view const& sym ) const {
		return _openers.finds_pair(sym);
	}
	void binder( std::string_view const& binder, int llevel, int rlevel ) {
		_binders.emplace(binder,Binder{llevel,rlevel,{}});
	}
	auto finds_binder( std::string_view const& binder ) const& {
		return _binders.finds_pair(binder);
	}
	void binder_mid(
		std::string_view const& prefix,
		std::string_view const& mid,
		std::string_view const& actual,
		Opt<std::string> const& cons 
	) & {
		auto x = _binders.finds_pair(prefix);
		if( !x ) throw Error("\"binder not registered\"")(prefix)(mid);
		auto& [sym,binder] = *x;
		binder.bbinds.emplace(mid,std::pair{std::string(actual),cons});
		_pretty_of.emplace(actual,BinderRel{binder.llevel,binder.rlevel,std::string(prefix),std::string(mid),cons});
	}
	void empty_compr( std::string const& opener, std::string const& closer, std::string_view const& actual, int level ) & {
		auto const& [it,fl] = _openers.emplace(opener,Opener{level,closer});
		it->second.empty.emplace(actual);
		_pretty_of.emplace(actual,Empty{opener,closer});
		_postfixes.emplace(closer,{level,closer});
	}
	void singleton_compr( std::string const& opener, std::string const& closer, std::string_view const& actual, int level ) & {
		auto const& [it,fl] = _openers.emplace(opener,Opener{level,closer});
		it->second.singleton.emplace(actual);
		_pretty_of.emplace(actual,Singleton{opener,closer});
		_postfixes.emplace(closer,{level,closer});
	}
	void compr( std::string const& opener, std::string const& closer, std::string_view const& actual, int level ) & {
		auto const& [it,fl] = _openers.emplace(opener,Opener{level,closer});
		it->second.compr.emplace(actual);
		_pretty_of.emplace(actual,Compr{opener,closer});
		_postfixes.emplace(closer,{level,closer});
	}
	void bcompr( std::string const& opener, std::string const& mid, std::string const& closer, std::string_view const& actual, Opt<std::string> const& cons, int level ) & {
		auto const& [it,fl] = _openers.emplace(opener,Opener{level,closer});
		it->second.bcompr.emplace(mid,std::pair{actual,cons});
		_pretty_of.emplace(actual,ComprRel{opener,mid,closer,cons});
		_postfixes.emplace(closer,{level,closer});
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