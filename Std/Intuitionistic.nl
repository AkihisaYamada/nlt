
---
# Type-Free Intuitionistic Logic

We can obtain `false` via `∀P. P` to satisfy the law of explosion.
---
obtain false where
	false_elim#elim
		-- @English Law of Explosion
		-- @Latin ex falso quodlibet
		if false then P;
	- for thesis if assm: ∀false. (false ⟹ ∀P. P) ⟹ thesis then thesis;
		apply assm[of (∀P. P)].
	.
import Minimal.

begin

lemma not_imp_iff_false: if nP: ¬P then P ⟺ false;
	by iff_intro not_imp_false[OF nP].

lemma not_elim: if nP: ¬P, P: P then Q;
	use not_imp_false[OF nP P].

lemma false_imp_iff#simp (false ⟹ P) ⟺ true;
	by iff_true.

interpret and: iff.MetaCommAbsorb (∧) false;
	by iff_intro.

note#simp and.left_absorb and.right_absorb.

interpret or: iff.MetaCommNeutral (∨) false;
	by iff_intro or_intro #elim or_elim false_elim.

note#simp or.left_neutral or.right_neutral.

extend ExcludedMiddle begin
	interpret Classical;
		- if nnP: ¬ ¬ P then P;
			apply cases[of P];
			- if nP: ¬P;
				by not_elim[OF nnP nP].
			.
		.
end
