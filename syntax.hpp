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

class Syntax : public Lex {
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
	struct Opener {
		std::string closer;
		int level;
		std::function<Term(Parser&)> handler;
	};
private:
	StrMap<Opener> _openers;
	StrSet _closers;
	StrMap<Prefix> _prefixes;
	StrMap<Infix> _infixes;
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
	void closer(std::string const& cl) {
		_closers.insert(cl);
	}
	bool has_closer(std::string_view const& sym) const {
		return _closers.contains(sym);
	}
	void encloser(std::string const& opener, std::string const& cl, int level, std::function<Term(Parser&)> handler) {
		_openers.insert({opener,{cl,level,handler}});
		closer(cl);
	}
	Opt<std::pair<std::string const, Opener> const&> finds_opener(std::string_view const& sym) const {
		return _openers.finds(sym);
	}
	std::function<std::ostream&(std::ostream&)> pretty_term(Term const& term, int level = -1000) const &;
	std::function<std::ostream&(std::ostream&)> pretty_cterm(CTerm const& term) const &;
	std::function<std::ostream&(std::ostream&)> pretty_thm(Thm const& thm) const &;
	std::function<std::ostream&(std::ostream&)> pretty_thms(StrMap<Thm> const& thms) const &;
	std::function<std::ostream&(std::ostream&)> pretty_ctxt(Ctxt const& ctxt) const &;
	std::function<std::ostream&(std::ostream&)> pretty_subst(CSubst const& subst) const &;
};

extern Syntax SYNTAX;

inline std::ostream& operator<<(std::ostream& os, Term const& t) {
	return os << SYNTAX.pretty_term(t,0);
}

inline std::ostream& operator<<(std::ostream& os, CSubst const& subst) {
	return os << SYNTAX.pretty_subst(subst);
}

inline std::ostream& operator<<(std::ostream& os, Ctxt const& ctxt) {
	return os << SYNTAX.pretty_ctxt(ctxt);
}

#endif