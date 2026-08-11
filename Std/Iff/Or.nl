import base? Std.Or.

begin

instance True, False.

lemma or_iff_true1#simp if ! P then P ∨ Q ⟺ true;
	by iff_intro or_intro1.

lemma or_iff_true2#simp if ! Q then P ∨ Q ⟺ true;
	by iff_intro or_intro2.

---
Algebraic properties of `(∨)`, with respect to `(⟺)`.
---
instance or: iff.MetaCompatible (∨);
	- if PQ: P ⟺ Q, RS: R ⟺ S then P ∨ R ⟺ Q ∨ S;
		by iff_intro #elim or_elim #simp PQ RS.
	.
note#cong or.cong.

lemma imp_or_if: if or: (P ⟹ Q) ∨ (P ⟹ R), !P then Q ∨ R;
	by or[unfold imp_imp_iff].

instance or: iff.MetaIdempotent (∨);
	by iff_intro #elim or_elim.

note#simp or.idem.

instance or: iff.MetaCommMonoidAbsorb (∨) true false;
	- by iff_intro or_intro #elim or_elim.
	- by iff_intro or_intro #elim or_elim.
	- by iff_intro #elim or_elim false_elim.
	- by iff_intro #elim or_elim.
	.

note#simp or.left_absorb or.right_absorb or.left_neutral or.right_neutral.

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

extend ExRel begin

	lemma ex_or_distrib: (∃x ⊏ a. P.[x] ∨ Q.[x]) ⟺ (∃x ⊏ a. P.[x]) ∨ (∃x ⊏ a. Q.[x]);
		apply iff_intro;
		-> if xa: x ⊏ a;
			apply or_elim[OF > _ _]>2;
			- by or_intro1 ex_intro1[OF _ xa].
			- by or_intro2 ex_intro1[OF _ xa].
			.
		apply or_elim[OF > _ _]>2;
		-> if xa: x ⊏ a;
			by ex_intro1[OF _ xa].
		-> if xa: x ⊏ a;
			by ex_intro1[OF _ xa].
		.

end

extend Iff_Not? Iff.Not begin

	instance base? base.Not.

	extend Iff_Not.MinimalNot begin

		instance base? base.MinimalNot.

		lemma nor_iff_not_nimp_nnot: ¬ (P ∨ Q) ⟺ ¬ (¬P ⟹ ¬ ¬ Q);
			apply iff_intro;
			- if nor;
				apply nor_elim[OF nor];
				by nimp_intro #simp nnnot_iff.
			- if nimp;
				apply nor_intro;
				- by nimp_not_elim1[OF nimp, unfold nnnot_iff].
				- by nimp_elim2[OF nimp, unfold nnnot_iff].
				.
			.

		lemma nnot_nor_iff: ¬ (¬ ¬ P ∨ Q) ⟺ ¬ (P ∨ Q);
			unfold nor_iff_not_nimp_nnot nnnot_iff.

		lemma nor_nnot_iff: ¬ (P ∨ ¬ ¬ Q) ⟺ ¬ (P ∨ Q);
			unfold nor_iff_not_nimp_nnot nnnot_iff.

		extend Iff.And begin

			instance and_not: And.Not.
			instance and_not.MinimalNot.

			lemma nor_iff_and: ¬(P ∨ Q) ⟺ ¬P ∧ ¬Q;
				unfold nor_iff_not_nimp_nnot;
				unfold nimp_not_iff_and;
				unfold nnnot_iff.

		end

	end

end

