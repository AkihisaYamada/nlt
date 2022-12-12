#ifndef _syntax_hpp
#define _syntax_hpp

#include<iostream>
#include"core.hpp"
#include"lexer.hpp"

inline std::ostream& operator<<(
	std::ostream& stream, 
	const std::function<std::ostream& (std::ostream&)>& manipulator
) {
    return manipulator( stream );
}

class Syntax : public Lexer {
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
		String closer;
		int level;
		std::function<Term(std::function<std::optional<Term>(int)>)> handler;
	};
	StrMap<Prefix> prefixes;
	StrMap<Infix> infixes;
	StrMap<Opener> openers;
	StrSet closers;

public:
	struct Error : std::exception {
		String message;
		Error(String const& message) : message(message) {}
	};
	Syntax(std::istream& is);

	void prefix(String const& sym, int level, int rlevel) {
		prefixes.insert({sym,{level,rlevel}});
	}
	void infix(String const& sym, int level, int llevel, int rlevel) {
		infixes.insert({sym,{level,llevel,rlevel}});
	}
	void encloser(String const& opener, String const& closer, int level, std::function<Term(std::function<std::optional<Term>(int)>)> handler) {
		openers.insert({opener,{closer,level,handler}});
		closers.insert(closer);
	}
	std::function<std::ostream&(std::ostream&)> pretty_term(Term const& term, int level = -1000) const;
	std::function<std::ostream&(std::ostream&)> pretty_thm(Thm const& thm) const;
	std::function<std::ostream&(std::ostream&)> pretty_thms(StrMap<Thm> const& thms) const;
	std::function<std::ostream&(std::ostream&)> pretty_ctxt(Ctxt const& ctxt) const;
	std::optional<std::string> gets_thm_name();
	std::string get_thm_name();
	std::optional<Term> gets_term(int level = 0);
	Term get_term(int level = 0);
};
#endif