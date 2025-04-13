------
# Quantified Intuitionistic Logic

False can be obtained using universal quantifier.
------
fix prop (¬) (∧) (∨) (⟺) (∀:) (∃:).

import Prop.
import TypedAll.

interpret TypedFalse;
	obtain false where false_type: prop false, false_elim: false ⟹ ∀P. prop P ⟹ P;
		- for thesis, if assm;
			apply assm[of (∀P:prop. P)];
			- .
			- if all: ∀P : prop. P;
				by all_elim1[of P prop, OF all].
			.
		.
	by false_type #elim false_elim.

import TypedNot.
import TypedIff.
import TypedAnd.
import TypedOr.
import TypedEx.

begin

interpret QuantifiedMinimal.
interpret PropositionalIntuitionistic.

setup rewrite iff_imp iff_imp_rev iff.refl iff.trans.
setup dual iff.sym.

lemma ex_false_iff: (∃x:ι. false) ⟺ false;
	by not_imp_iff_false nex_false.
