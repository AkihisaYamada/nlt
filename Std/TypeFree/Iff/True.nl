---
## True
---
obtain true where true_intro! true;
	- for thesis if assm: ∀true. true ⟹ thesis then thesis;
		by assm[of (∀x. x ⟹ x)].
	.

interpret imp: iff.MetaLeftNeutral (⟹) true;
	by imp_imp_iff.

interpret imp: iff.MetaRightAbsorb (⟹) true;
	by iff_intro.

interpret iff: iff.MetaCommNeutral (⟺) true;
	by iff_intro #elim iff_elim.

note#simp imp.left_neutral imp.right_absorb iff.left_neutral iff.right_neutral.

lemma iff_true: P ⟹ P ⟺ true.
