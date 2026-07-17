---
## Conjunction via Iff
---	
fix (∧).
assume and_iff: P ∧ Q ⟺ (∀R. (P ⟹ Q ⟹ R) ⟹ R).

begin

interpret base? TypeFree.And;
	- for P Q if P: P, Q: Q then P ∧ Q;
		unfold and_iff;
		- if PQR: P ⟹ Q ⟹ R	then R;
			by PQR[OF P Q].
		.
	- if PQ: P ∧ Q then P;
		by PQ[unfold and_iff].
	- if PQ: P ∧ Q then Q;
		by PQ[unfold and_iff].
	.

interpret and: iff.MetaCompatible (∧);
	- if P: P ⟺ P', Q: Q ⟺ Q' then P ∧ Q ⟺ P' ∧ Q';
		by iff_intro #simp P Q.
	.

lemma and_cong1#cong if P: P ⟺ P', Q: P' ⟹ Q ⟺ Q' then P ∧ Q ⟺ P' ∧ Q';
	by iff_intro #simp P Q.

interpret and: iff.MetaIdempotent (∧);
	by iff_intro.

interpret and: iff.MetaCommSemigroup (∧);
	by iff_intro.

lemma and_imp_iff_imp_imp#simp#rule (P ∧ Q ⟹ R) ⟺ (P ⟹ Q ⟹ R);
	by iff_intro.

lemma imp_and_iff1#simp if P: P then P ∧ Q ⟺ Q;
	by iff_intro P.

lemma imp_and_iff2#simp if Q: Q then P ∧ Q ⟺ P;
	by iff_intro Q.

lemma and_iff: P ∧ Q ⟺ (∀R. (P ⟹ Q ⟹ R) ⟹ R);
	apply iff_intro;
	- simp imp_imp_iff.
	- if assm;
		apply assm.
	.

lemma iff_iff_and: (P ⟺ Q) ⟺ (P ⟹ Q) ∧ (Q ⟹ P);
	by iff_intro #elim iff_elim.

lemma imp_and_distrib: (P ⟹ Q ∧ R) ⟺ (P ⟹ Q) ∧ (P ⟹ R);
	apply iff_intro;
	- if imp;
		apply and_intro;
		- if P;
			apply and_elim[OF imp[OF P]].
		- if P;
			apply and_elim[OF imp[OF P]].
		.
	.

lemma all_and_distrib: (∀x. P.[x] ∧ Q.[x]) ⟺ (∀x. P.[x]) ∧ (∀x. Q.[x]);
	apply iff_intro;
	- if ab: ∀x. P.[x] ∧ Q.[x];
		apply and_intro;
		- by and_elim1[OF ab].
		- by and_elim2[OF ab].
		.
	.

interpret and: iff.MetaCommMonoidAbsorb (∧) false true;
	by iff_intro.

note#simp and.left_neutral and.right_neutral and.left_absorb and.right_absorb.

extend Iff? Iff.Not begin

	interpret base? base.Not.

	extend MinimalNot begin

		interpret base.ContraPos.
		interpret Iff.MinimalNot.

		lemma nimp_not_iff_and: ¬(P ⟹ ¬Q) ⟺ ¬ ¬ P ∧ ¬ ¬ Q;
			apply iff_intro;
			- if nimp;
				apply nimp_not_elim[OF nimp].
			simp;
			apply imp_commute>1;
			unfold nnot_imp_iff;
			by nimp_intro.

		lemma nand_iff_imp_not: ¬(P ∧ Q) ⟺ (P ⟹ ¬Q);
			unfold not_iff_imp_not_true.

		note imp_not_iff_nand: nand_iff_imp_not[dual].
			
		lemma nand_nnot_iff: ¬ (P ∧ ¬ ¬ Q) ⟺ ¬ (P ∧ Q);
			unfold+ nand_iff_imp_not nnnot_iff.

		lemma nnot_nand_iff: ¬ (¬ ¬ P ∧ Q) ⟺ ¬ (P ∧ Q);
			unfold and.commute;
			unfold nand_nnot_iff.

		lemma nnand_iff: ¬ ¬ (P ∧ Q) ⟺ ¬ ¬ P ∧ ¬ ¬ Q;
			apply iff_intro;
			- if nnand;
				apply+ and_intro nnand[THEN not_imp_imp_not];
				by #intro? nand_intro1 nand_intro2.
			fold nnot_nand_iff;
			by #simp imp_and_iff1.

	end

end
