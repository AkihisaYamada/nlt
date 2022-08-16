#ifndef _syntax_hpp
#define _syntax_hpp

#include<iostream>
#include"core.hpp"
#include"lexer.hpp"

inline std::ostream& operator<<(
        std::ostream& stream, 
        const std::function<std::ostream& (std::ostream&)>& manipulator) {
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
	typedef map<String,Prefix,less<>> PrefixTable;
	typedef map<String,Infix,less<>> InfixTable;

	PrefixTable prefixes;
	InfixTable infixes;

public:
	Syntax(istream& is) : Lexer(is) {}

	Syntax& prefix(String const& sym, int level, int rlevel) {
		prefixes.insert({sym,{level,rlevel}});
		return *this;
	}
	Syntax& infix(String const& sym, int level, int llevel, int rlevel) {
		infixes.insert({sym,{level,llevel,rlevel}});
		return *this;
	}

	function<ostream&(ostream&)> pretty_term(Term const& term, int level = -1000) const;
	function<ostream&(ostream&)> pretty_thm(Thm const& thm) const;
	function<ostream&(ostream&)> pretty_ctxt(Ctxt const& ctxt) const;
	string get_thm_name();
	optional<Term> get_term(int level = 0);
	Thm get_thm(Ctxt const& ctxt);
};
#endif