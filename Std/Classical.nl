---
# Type-Free Classical Logic
---
import Minimal.
import DoubleNegation.

begin

lemma nnot_iff#simp ¬ ¬ P ⟺ P;
	apply iff_intro[OF nnot_imp nnot_intro].

lemma or_iff_nand: P ∨ Q ⟺ ¬ (¬P ∧ ¬Q);
	fold nor_iff.

interpret Intuitionistic;
	retain false;
		- if 0: false then P;
			apply contradiction;
			by 0.
		.
	.
interpret PierceLaw;
	- if PQP: (P ⟹ Q) ⟹ P then P;
		apply nnot_imp;
		-> if nP: ¬P then false;
			apply not_imp_false[OF nP];
			apply PQP;
			- if P: P then Q;
				by not_elim[OF nP P].
			.
		.
	.
