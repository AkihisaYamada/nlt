---
## Negation via Free False
---

fix false (¬).

assume not_intro: if P ⟹ false then ¬P.
assume not_imp_false#intro?[after 1] if ¬P, P then false.

begin

lemma not_false! ¬false;
	by not_intro.

lemma false_imp_not: if 0: false then ¬P;
	by not_intro 0.

lemma imp_not_imp_false: if P: P, nP: ¬ P then false;
	apply not_imp_false[OF nP P].

lemma imp_not: if P: P, nQ: ¬Q then ¬(P ⟹ Q);
	apply not_intro;
	- if PQ: P ⟹ Q;
		by nQ PQ[OF P].
	.

lemma imp_not_imp: if PQ: P ⟹ Q then ¬Q ⟹ ¬P;
	by not_intro PQ.

lemma self_refutation: if PnP: P ⟹ ¬P then ¬P;
	apply not_intro;
	- if P: P then false;
		by not_imp_false[OF PnP[OF P] P].
	.

lemma not_imp_imp_not: if nP: ¬P, QP: Q ⟹ P then ¬Q;
	by imp_not_imp[OF QP nP].

lemma imp_not_sym: if PnQ: P ⟹ ¬Q then Q ⟹ ¬P;
	by not_intro #elim PnQ.

lemma nimp_imp_not: if nimp: ¬(P ⟹ Q) then ¬Q;
	apply not_intro;
	by not_imp_false[OF nimp].

lemma nimp_not_imp_not: if nimpn: ¬(P ⟹ ¬Q) then ¬ ¬ P;
	apply not_intro;
	- if nP: ¬P then false;
		apply not_imp_false[OF nimpn];
		- if P: P then ¬Q;
			apply not_intro;
			by not_imp_false[OF nP P].
		.
	.

lemma nnot_intro: P ⟹ ¬ ¬ P;
	by not_intro.

lemma nnot_imp_imp: if imp: ¬ ¬ P ⟹ Q then P ⟹ Q;
	by imp nnot_intro.

lemma not_imp_not_all: ¬ P.[x] ⟹ ¬(∀y. P.[y]);
	by not_intro.

lemma nnot_imp_nnot: if nnP: ¬ ¬ P, PQ: P ⟹ Q then ¬ ¬ Q;
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

lemma nnimp_imp_nnot: if nnPQ: ¬ ¬ (P ⟹ Q), P: P then ¬ ¬ Q;
	apply not_intro;
	- if nQ: ¬Q;
		have nPQ: ¬(P ⟹ Q);
			apply not_intro;
			- if PQ: P ⟹ Q;
				by nQ PQ[OF P].
			.
		use nnPQ nPQ.
	.

lemma nnall_imp: if nnall: ¬ ¬ (∀x. P.[x]) then ∀x. ¬ ¬ P.[x];
	by not_imp_imp_not[OF nnall not_imp_not_all].

extend Iff begin

	interpret? FalseNot;
		- show: ¬ P ⟺ (P ⟹ false);
			apply iff_intro;
			- apply not_imp_false>0.
			- apply not_intro>0.
			.
		.

end
