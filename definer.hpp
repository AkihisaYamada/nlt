#ifndef _DEFINER_HPP_
#define _DEFINER_HPP_

#include "theory.hpp"
#include "rewrite.hpp"

class Definer {
	Thy _thy;
	std::string const EQ;
	Term const LAM;
	Thm const refl;// ∀P. P = P
	Thm _beta;
	struct _Init {
		Thy thy;
		std::string EQ;
		Term LAM;
		Thm beta;
		Thm refl;
	};
	Definer( _Init && init ) :
		_thy(std::move(init.thy)), LAM(std::move(init.LAM)), EQ(std::move(init.EQ)), _beta(std::move(init.beta)), refl(std::move(init.refl)) {}
	static _Init _init( Thy const& thy, Thm const& beta );
public:
	Definer( Thy const& thy, Thm const& beta ) : Definer(_init(thy,beta)) {}
	Thm beta() const {
		return _beta;
	}
	std::pair<std::string,Thm> define(Thy& thy, Term const& l, Term const& r, Opt<std::string const&> name) const;
};


#endif
