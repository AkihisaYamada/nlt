#ifndef _DEFINER_HPP_
#define _DEFINER_HPP_

#include "rewriter.hpp"

class Definer {
	Ref<Rewriter const> rewriter;
	std::string const EQ;
	Term const LAM;
	Rewriter::Rules beta;
public:
	struct Error : std::exception {
		Term term;
		Error(Term const& term) : term(term) {}
	};
	Definer(Ref<Rewriter const> const& rewriter, std::string const& EQ, Term const& LAM, Thm const& beta) :
		rewriter(rewriter), LAM(LAM), EQ(EQ)
	{
		this->beta.add(beta);
	}
	void define(Ctxt& ctxt, Term const& l, Term const& r, Opt<std::string> const& name) const;
};


#endif
