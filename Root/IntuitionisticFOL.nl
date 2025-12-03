------
# Quantified Intuitionistic Logic

False can be obtained using universal quantifier.
------
import Base.

fix (:) prop (¬) (∧) (∨) (⟺) (∀:) (∃:).

import Prop.
import TypedAll.

import IntuitionisticPL;
	obtain false where ! false : prop, false_elim: false ⟹ ∀P. P : prop ⟹ P;
		- for thesis if assm;
			apply assm[of (∀P:prop. P)];
			- .
			- if all: ∀P : prop. P;
				by all_elim1[of P prop, OF all].
			.
		.
	retain false := false.
	- false ⟹ ∀P. P : prop ⟹ P;
		by #elim false_elim.
	.
import TypedEx.

begin

interpret MinimalFOL;
	retain false; .
	.

lemma ex_false_iff: (∃x:ι. false) ⟺ false;
	by not_imp_iff_false nex_false.
