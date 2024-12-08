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
		Ref<Rewriter const> const& rewriter;
		std::string const& EQ;
		Term const& LAM;
		Thm const& beta;
		Thm const& refl;
	};
	Definer( _Init const& init ) :
		rewriter(init.rewriter), LAM(init.LAM), EQ(init.EQ), beta(rewriter->make_rules()), refl(init.refl)
	{
		rewriter->add_rule(this->beta,init.beta);
	}
	static _Init _init(Ref<Rewriter const> const& rewriter, Thm const& beta);
public:
	Definer(Ref<Rewriter const> const& rewriter, Thm const& beta) : Definer(_init(rewriter,beta)) {}
	std::pair<std::string,Thm> define(Locale& loc, Term const& l, Term const& r, Opt<std::string const&> name) const;
};


#endif
