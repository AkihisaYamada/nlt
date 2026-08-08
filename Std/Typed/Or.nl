---
## Type-Free Disjunction
---
fix (∨).
import or: Magma Prop (∨).
assume or_intro1: if P, P : Prop, Q : Prop then P ∨ Q.
assume or_intro2: if Q, P : Prop, Q : Prop then P ∨ Q.
assume or_elim: if P ∨ Q, P ⟹ R, Q ⟹ R, P : Prop, Q : Prop, R : Prop then R.

begin

note! or.closed.

lemma or_intro:
	if assm: ∀R. (P ⟹ R) ⟹ (Q ⟹ R) ⟹ R : Prop ⟹ R, [P : Prop, Q : Prop] then P ∨ Q;
	apply assm;
	- by or_intro1.
	by or_intro2.

instance or: Symmetric Prop (∨);
	- if PQ: P ∨ Q, ...;
		apply or_elim[OF PQ];
		- by or_intro2.
		by or_intro1.
	.

extend Not begin

	extend ContraPos begin

		lemma nor_elim1: if nor: ¬(P ∨ Q), [P : Prop, Q : Prop] then ¬P;
			apply not_imp_imp_not[OF nor];
			by or_intro1.

		lemma nor_elim2: if nor: ¬(P ∨ Q), [P : Prop, Q : Prop] then ¬Q;
			apply not_imp_imp_not[OF nor];
			by or_intro2.

		lemma nor_elim: if nor: ¬(P ∨ Q), assm: ¬P ⟹ ¬Q ⟹ R, [P : Prop, Q : Prop, R : Prop] then R;
			by assm[OF nor_elim1[OF nor ! !] nor_elim2[OF nor ! !]].

	end

	extend MinimalNot begin

		instance .ContraPos.

		lemma nor_intro: if nP: ¬P, nQ: ¬Q, [P : Prop, Q : Prop] then ¬(P ∨ Q);
			apply imp_not_imp_not;
			- if or: P ∨ Q;
				apply or_elim[OF or];
				- by not_elim_not[OF nP].
				- by not_elim_not[OF nQ].
				.
			.

		lemma nnot_excluded_middle: if [P :	Prop] then ¬ ¬ (P ∨ ¬P);
			apply imp_not_imp_not;
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
			if [P : Prop] then P ∨ ¬P;
			apply cases[of P];
			- by or_intro1.
			- by or_intro2.
			.

	end
end
