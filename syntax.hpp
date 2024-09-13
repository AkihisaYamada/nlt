#ifndef _syntax_hpp
#define _syntax_hpp

#include<iostream>
#include"core.hpp"
#include"lexer.hpp"

template<class I, class T>
void out_sep(
	std::ostream& os, I it, I const& end, std::string const& sep,
	std::function<void(std::ostream&,T const&)> const& elm = [](std::ostream& os, T const& e){os << e;}
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
	StrMap<Prefix> _prefixes;
	StrMap<Infix> _infixes;
	StrMap<Opener> _openers;
	StrSet _closers;
	friend Parser;
public:
	Syntax();
	void prefix(std::string const& sym, int level, int rlevel) {
		_prefixes.insert({sym,{level,rlevel}});
	}
	void infix(std::string const& sym, int level, int llevel, int rlevel) {
		_infixes.insert({sym,{level,llevel,rlevel}});
	}
	void encloser(std::string const& opener, std::string const& closer, int level, std::function<Term(Parser&)> handler) {
		_openers.insert({opener,{closer,level,handler}});
		_closers.insert(closer);
	}
	std::function<std::ostream&(std::ostream&)> pretty_term(Term const& term, int level = -1000) const &;
	std::function<std::ostream&(std::ostream&)> pretty_thm(Thm const& thm) const &;
	std::function<std::ostream&(std::ostream&)> pretty_thms(StrMap<Thm> const& thms) const &;
	std::function<std::ostream&(std::ostream&)> pretty_ctxt(Ctxt const& ctxt) const &;
	std::function<std::ostream&(std::ostream&)> pretty_subst(CSubst const& subst) const &;
};

class Parser : public Syntax, public Lexer {

public:
	struct Error : std::exception {
		std::string message;
		Error(std::string const& message) : message(message) {}
	};
	Parser( std::istream& is ) : Lexer(*this,is) {}
	Opt<std::string> gets_thm_name();
	std::string get_thm_name();
	Opt<Term> gets_term(int level = 0);
	Term get_term(int level = 0);
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