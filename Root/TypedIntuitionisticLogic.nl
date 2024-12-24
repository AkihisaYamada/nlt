------
# Typed Intuitionistic Logic
------

base Root;

fix prop (∧) (∨) (⟺) (¬) (∃);

import Prop;
import PropTrue;
import PropFalse;
import PropAnd;
import PropIff;
import PropOr;
import not: Unary prop (¬);
import ex: Binder prop (∃);

import TypeFreeIntuitionistic;
import PropOr;
import PropEx;

setup rewrite iff.refl iff.sym iff.trans iff_elim1;
setup cong
	iff_cong_imp: P ⟹ Q,
	iff_cong_iff: P ⟺ Q,
	iff_cong_and: P ∧ Q,
	iff_cong_not: ¬P,
	iff_cong_all! ∀x. α.[x];

setup conclude iff.refl true_intro;

ctxt;

