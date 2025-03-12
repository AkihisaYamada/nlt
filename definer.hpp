#ifndef _DEFINER_HPP_
#define _DEFINER_HPP_

#include "locale.hpp"
#include "rewriter.hpp"

class Definer {
	Locale _loc;
	std::string const EQ;
	Term const LAM;
	Thm const refl;// ∀P. P = P
	Rewriter::Rules beta;
	struct _Init {
		Locale loc;
		std::string EQ;
		Term LAM;
		Thm beta;
		Thm refl;
	};
	Definer( _Init && init ) :
		_loc(std::move(init.loc)), LAM(std::move(init.LAM)), EQ(std::move(init.EQ)), beta(_loc.rewriter().make_rules()), refl(std::move(init.refl)) {
		_loc.rewriter().add_rule(_loc,this->beta,std::move(init.beta));
	}
	static _Init _init( Locale const& loc, Thm const& beta );
public:
	Definer( Locale const& loc, Thm const& beta ) : Definer(_init(loc,beta)) {}
	std::pair<std::string,Thm> define(Locale& loc, Term const& l, Term const& r, Opt<std::string const&> name) const;
};


#endif
