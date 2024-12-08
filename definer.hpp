#ifndef _DEFINER_HPP_
#define _DEFINER_HPP_

#include "locale.hpp"
#include "rewriter.hpp"

class Definer {
	Ref<Rewriter const> rewriter;
	std::string const EQ;
	Term const LAM;
	Thm const refl;
	Rewriter::Rules beta;
	struct _Init {
		Ref<Rewriter const> rewriter;
		std::string EQ;
		Term LAM;
		Thm beta;
		Thm refl;
	};
	Definer( _Init && init ) :
		rewriter(std::move(init.rewriter)), LAM(std::move(init.LAM)), EQ(std::move(init.EQ)), beta(rewriter->make_rules()), refl(std::move(init.refl))
	{
		rewriter->add_rule(this->beta,std::move(init.beta));
	}
	static _Init _init(Ref<Rewriter const> const& rewriter, Thm const& beta);
public:
	Definer(Ref<Rewriter const> const& rewriter, Thm const& beta) : Definer(_init(rewriter,beta)) {}
	std::pair<std::string,Thm> define(Locale& loc, Term const& l, Term const& r, Opt<std::string const&> name) const;
};


#endif
