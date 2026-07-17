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
			apply not.cmono[OF _ nor];
			by or_intro1.

		lemma nor_elim2: if nor: ¬(P ∨ Q) then ¬Q;
			apply not.cmono[OF _ nor];
			by or_intro2.

		lemma nor_elim: if nor: ¬(P ∨ Q), assm: ¬P ⟹ ¬Q ⟹ R then R;
			by assm[OF nor_elim1[OF nor] nor_elim2[OF nor]].

	end

	extend MinimalNot begin

		interpret .ContraPos.

		lemma nor_intro: if nP: ¬P, nQ: ¬Q then ¬(P ∨ Q);
			apply self_refutation;
			- if or: P ∨ Q;
				apply or_elim[OF or];
				- by not_elim_not[OF nP].
				- by not_elim_not[OF nQ].
				.
			.

		lemma nnot_excluded_middle: ¬ ¬ (P ∨ ¬P);
			apply self_refutation;
			- if nor: ¬(P ∨ ¬P);
				apply nor_elim[OF nor];
				- if nP: ¬P, nnP: ¬ ¬ P;
					by not_elim_not[OF nnP nP].
				.
			.

	end

	extend ExcludedMiddle begin

		lemma or_not:
			-- @English excluded middle
			-- @Latin tertium non datur
			P ∨ ¬P;
			apply cases[of P];
			- by or_intro1.
			- by or_intro2.
			.

	end
end

extend Iff begin

	interpret? Or;
		- for P Q;
			apply iff_intro[OF or_elim or_intro].
		.
end