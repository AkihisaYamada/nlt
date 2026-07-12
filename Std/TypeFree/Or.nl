---
## Type-Free Disjunction
---
fix (∨).
assume or_intro1: if P then P ∨ Q.
assume or_intro2: if Q then P ∨ Q.
assume or_elim: if P ∨ Q, P ⟹ R, Q ⟹ R then R.

begin

lemma or_intro: if assm: ∀R. (P ⟹ R) ⟹ (Q ⟹ R) ⟹ R then P ∨ Q;
	apply assm;
	- by or_intro1.
	by or_intro2.

interpret or: MetaSymmetric (∨);
	- if PQ: P ∨ Q;
		apply or_elim[OF PQ];
		- by or_intro2.
		by or_intro1.
	.

extend Not begin

	extend ContraPos begin

		lemma nor_elim1: if nor: ¬(P ∨ Q) then ¬P;
			apply not.cmono[OF or_intro1].

		lemma nor_elim2: if nor: ¬(P ∨ Q) then ¬Q;
			apply not.cmono[OF or_intro2].

		lemma nor_elim: if nor: ¬(P ∨ Q), assm: ¬P ⟹ ¬Q ⟹ R then R;
			by assm[OF nor_elim1[OF nor] nor_elim2[OF nor]].

	end

	extend MinimalNot begin

		lemma nor_intro: if nP: ¬P, nQ: ¬Q then ¬(P ∨ Q);
			apply self_refutation;
			- if or: P ∨ Q;
				apply or_elim[OF or];
				- by not_elim_not[OF nP].
				- by not_elim_not[OF nQ].
				.
			.

		lemma nnot_excluded_middle: ¬ ¬ (P ∨ ¬P);
			apply not_intro;
			- if nor: ¬(P ∨ ¬P);
				apply not_imp_false[of (¬P)];
				by nor_elim[OF nor].
			.

	end

end

extend Iff begin

	interpret? Or;
		- for P Q;
			apply iff_intro[OF or_elim or_intro].
		.
end