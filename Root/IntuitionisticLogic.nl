------
# Typed Intuitionistic Logic
------

base Root;

fix prop (∧) (∨) (⟺) (¬) (∃);

import True;
import False;

-- We assume the logical constants and operations are well-typed.

import true: Member { for prop true; }
import false: Member { for prop false; }
import imp: Magma { for prop (⟹); }
import all: Binder { for prop (∀); }
import and: Magma { for prop (∧); }
import iff: Magma { for prop (⟺); }
import not: Unary { for prop (¬); }
import ex: Binder { for prop (∃); }

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

