---
# Minimal Not
---
fix false (¬).
assume not_intro: if P ⟹ false then ¬P.
assume not_imp_false#intro?[after 1] if ¬P, P then false.

begin

lemma not_false: ¬false;
	by not_intro.

lemma false_imp_not: if 0: false then ¬P;
	by not_intro 0.

lemma imp_not: if P: P, nQ: ¬Q then ¬(P ⟹ Q);
	apply not_intro;
	- if PQ: P ⟹ Q;
		by nQ PQ[OF P].
	.

lemma imp_not_imp: if PQ: P ⟹ Q then ¬Q ⟹ ¬P;
	by not_intro PQ.

lemma not_imp_imp_not: if nP: ¬P, QP: Q ⟹ P then ¬Q;
	by imp_not_imp[OF QP nP].

lemma imp_not_sym: if PnQ: P ⟹ ¬Q then Q ⟹ ¬P;
	by not_intro #elim PnQ.

lemma nnot_intro: P ⟹ ¬ ¬P;
	by not_intro.

lemma nnot_imp: if imp: ¬ ¬P ⟹ Q then P ⟹ Q;
	by imp nnot_intro.

lemma not_imp_not_all: ¬ P.[x] ⟹ ¬(∀y. P.[y]);
	by not_intro.

lemma nnot_imp_nnot: if nnP: ¬ ¬P, PQ: P ⟹ Q then ¬ ¬Q;
	apply not_intro;
	- if nQ: ¬Q;
		use nnP;
		by imp_not_imp[OF PQ nQ].
	.

lemma nnot_not_imp_nimp: if nnP: ¬ ¬ P, ! ¬Q then ¬(P ⟹ Q);
	apply not_intro;
	- if PQ: P ⟹ Q;
		by nnot_imp_nnot[OF nnP PQ].
	.

lemma nnimp_imp_nnot: if nnPQ: ¬ ¬(P ⟹ Q), P: P then ¬ ¬Q;
	apply not_intro;
	- if nQ: ¬Q;
		have nPQ: ¬(P ⟹ Q);
			apply not_intro;
			- if PQ: P ⟹ Q;
				by nQ PQ[OF P].
			.
		use nnPQ nPQ.
	.
