fix (∨).
assume or_iff: P ∨ Q ⟺ (∀R. (P ⟹ R) ⟹ (Q ⟹ R) ⟹ R).

begin

interpret or: iff.MetaAbsorb (∨) true;
	by iff_intro #simp or_iff.

note#simp or.left_absorb or.right_absorb.

interpret base? TypeFree.Or;
	- if P: P then P ∨ Q;
		unfold or_iff iff_true[OF P].
	- if Q: Q then P ∨ Q;
		unfold or_iff iff_true[OF Q].
	- if PQ: P ∨ Q, PR: P ⟹ R, QR: Q ⟹ R then R;
		by PQ[unfold or_iff, OF PR QR].
	.

lemma or_iff_true1#simp if ! P then P ∨ Q ⟺ true;
	by iff_intro or_intro1.

lemma or_iff_true2#simp if ! Q then P ∨ Q ⟺ true;
	by iff_intro or_intro2.


---
Algebraic properties of `(∨)`, with respect to `(⟺)`.
---
interpret or: iff.MetaCompatible (∨);
	- if PQ: P ⟺ Q, RS: R ⟺ S then P ∨ R ⟺ Q ∨ S;
		by iff_intro #elim or_elim #simp PQ RS.
	.
note#cong or.cong.

lemma imp_or_if: if or: (P ⟹ Q) ∨ (P ⟹ R), !P then Q ∨ R;
	by or[unfold imp_imp_iff].

interpret or: iff.MetaIdempotent (∨);
	- show: P ∨ P ⟺ P;
		by iff_intro #elim or_elim.
	.

note#simp or.idem.

interpret or: iff.MetaCommSemigroupAbsorb (∨) true;
	by iff_intro #elim or_elim #simp or_iff_true1 or_iff_true2.

extend False begin

	interpret or: iff.MetaCommMonoid (∨) false true;
		by iff_intro or_intro #elim or_elim false_elim.

	note#simp or.left_neutral or.right_neutral.

end

extend And begin

	lemma or_imp_iff: (P ∨ Q ⟹ R) ⟺ (P ⟹ R) ∧ (Q ⟹ R);
		apply iff_intro;
		- if imp;
			by imp.
		by #elim or_elim.

	lemma and_or_distrib: P ∧ (Q ∨ R) ⟺ P ∧ Q ∨ P ∧ R;
		apply iff_intro;
		simp or_imp_iff.

	lemma or_and_distrib: (P ∨ Q) ∧ R ⟺ P ∧ R ∨ Q ∧ R;
		unfold and.commute;
		unfold and_or_distrib.

end

extend Iff.FalseNot begin

	interpret base? base.FalseNot.

	lemma nor_iff_nimp: ¬ (P ∨ Q) ⟺ ¬(¬P ⟹ ¬ ¬ Q);
		apply iff_intro;
		-> if nor, imp;
			apply not_imp_false[of (¬Q)];
			use nor;
			by imp #elim nor_elim.
		-> if nimp, or;
			apply not_imp_false[OF nimp];
			- if nP: ¬P then ¬ ¬ Q;
				apply or_elim[OF or];
				- if P;
					apply not_intro;
					by not_imp_false[OF nP P].
				by nnot_intro.
			.
		.

	lemma nnot_nor_iff: ¬ (¬ ¬ P ∨ Q) ⟺ ¬ (P ∨ Q);
		unfold nor_iff_nimp nnnot_iff.

	lemma nor_nnot_iff: ¬ (P ∨ ¬ ¬ Q) ⟺ ¬ (P ∨ Q);
		unfold nor_iff_nimp nnnot_iff.

	extend Or.And begin

		lemma nor_iff: ¬ (P ∨ Q) ⟺ ¬P ∧ ¬Q;
			unfold not_iff_imp_false;
			by or_imp_iff.

	end

end

