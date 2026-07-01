---
## Deriving Conjunction
---

fix (∧).
assume and_iff: P ∧ Q ⟺ (∀R. (P ⟹ Q ⟹ R) ⟹ R).

begin

interpret And;
	- if P: P, Q: Q then P ∧ Q;
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
		by iff_intro #unfold P Q.
	.
note(cong) and.cong.

interpret and: iff.MetaIdempotent (∧);
	by iff_intro.

interpret and: iff.MetaAssociative (∧);
	by iff_intro.

interpret and: iff.MetaCommNeutral (∧) true;
	by iff_intro.

note(simp) and.left_neutral and.right_neutral.

lemma and_cong1: if P: P ⟺ P', Q: P' ⟹ Q ⟺ Q' then P ∧ Q ⟺ P' ∧ Q';
	by iff_intro #unfold P Q.

lemma and_imp_iff_imp_imp(simp) (P ∧ Q ⟹ R) ⟺ (P ⟹ Q ⟹ R);
	by iff_intro.

lemma imp_and_iff1: if P: P then P ∧ Q ⟺ Q;
	by iff_intro P.

lemma imp_and_iff2: if Q: Q then P ∧ Q ⟺ P;
	by iff_intro Q.

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
