-------
# Type-Free Intuitionistic Logic
-------
import Base.

-- Obtains false, which derives everything, including non-propositions.
obtain false where false_elim: false ⟹ ∀P. P;
	for thesis if assm: ∀false. (false ⟹ ∀P. P) ⟹ thesis then thesis;
		by assm[of (∀P. P)].
	.

import TypeFreeMinimal.

begin

lemma not_imp_iff_false: if nP: ¬P then P ⟺ false;
	apply iff_intro;
	- by not_imp_false[OF nP].
	by #elim false_elim.

lemma false_imp_iff: (false ⟹ P) ⟺ true;
	by iff_true #elim false_elim.

lemma false_and_iff: false ∧ P ⟺ false;
	by iff_intro #elim and_elim false_elim.

lemma and_false_iff: P ∧ false ⟺ false;
	unfold iff.and.commute;
	by false_and_iff.

lemma not_elim: if nP: ¬P, P: P then Q;
	by false_elim[OF not_imp_false[OF nP P]].
