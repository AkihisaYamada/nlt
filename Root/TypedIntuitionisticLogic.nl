------
# Typed Intuitionistic Logic
------

base Root;

fix prop (∧) (∨) (⟺) (¬) (∃);

import Prop;
import True;
import False;

-- We assume the logical constants and operations are well-typed.

import imp: Magma prop (⟹);
import all: Binder prop (∀);
import true: Member prop true;
import false: Member prop false;
import and: Magma prop (∧);
import iff: Magma prop (⟺);
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

