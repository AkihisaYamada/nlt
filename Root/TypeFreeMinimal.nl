-------
# Type-Free Minimal Logic
-------

import True.

fix false (¬) (∧) (⟺) (∨) (∃).
assume and_intro: P ⟹ Q ⟹ P ∧ Q.
assume and_elim1: P ∧ Q ⟹ P.
assume and_elim2: P ∧ Q ⟹ Q.

assume not_imp_false: ¬ P ⟹ P ⟹ false.
assume not_intro: (P ⟹ false) ⟹ ¬ P.

assume iff_intro: (P ⟹ Q) ⟹ (Q ⟹ P) ⟹ P ⟺ Q.
assume iff_elim1: (P ⟺ Q) ⟹ P ⟹ Q.
assume iff_elim2: (P ⟺ Q) ⟹ Q ⟹ P.

assume or_intro1: P ⟹ P ∨ Q.
assume or_intro2: for P Q, Q ⟹ P ∨ Q.
assume or_elim: P ∨ Q ⟹ ∀R. (P ⟹ R) ⟹ (Q ⟹ R) ⟹ R.

assume ex_intro1: for x, α.[x] ⟹ ∃x. α.[x].
assume ex_elim: (∃x. α.[x]) ⟹ ∀P. (∀x. α.[x] ⟹ P) ⟹ P.

begin
---
## Theorems
---

---
### If-and-only-if
---

interpret iff: MetaEquivalence (⟺);
	- for P Q, if PQ: P ⟺ Q then Q ⟺ P;
		by iff_intro[OF iff_elim2[OF PQ] iff_elim1[OF PQ]].
	- by iff_intro[OF imp.refl imp.refl].
	- for P Q R, if PQ: P ⟺ Q, QR: Q ⟺ R then P ⟺ R;
		note PR: imp.trans[OF iff_elim1[OF PQ] iff_elim1[OF QR]].
		note RP: imp.trans[OF iff_elim2[OF QR] iff_elim2[OF PQ]].
		by iff_intro[OF PR RP].
	.

note! iff.refl.

setup rewrite iff_elim1 iff_elim2 iff.refl iff.trans.
setup dual iff.sym.

lemma iff_cong_imp#cong: for P R, if PQ: P ⟺ Q, RS: R ⟺ S then (P ⟹ R) ⟺ (Q ⟹ S);
	apply iff_intro,
	- if PR: P ⟹ R, [Q] then S;
		by iff_elim1[OF RS] PR iff_elim2[OF PQ].
	- if QS: Q ⟹ S, [P] then R;
		by iff_elim2[OF RS] QS iff_elim1[OF PQ].
	.

lemma iff_cong_iff#cong: for P R, if PQ: P ⟺ Q, RS: R ⟺ S then (P ⟺ R) ⟺ (Q ⟺ S);
	apply iff_intro,
	- if PR: P ⟺ R then Q ⟺ S;
		have QR: Q ⟺ R;
			by iff.trans[OF iff.sym[OF PQ] PR].
		by iff.trans[OF QR RS].
	- if QS: Q ⟺ S then P ⟺ R;
		have PS: P ⟺ S;
			by iff.trans[OF PQ QS].
		by iff.trans[OF PS iff.sym[OF RS]].
	.

lemma iff_cong_all#cong: if ab: ∀x. α.[x] ⟺ β.[x] then (∀x. α.[x]) ⟺ (∀x. β.[x]);
	apply iff_intro,
	- if [∀x. α.[x]] then ∀x. β.[x];
		by iff_elim1[OF ab].
	- if [∀x. β.[x]] then ∀x. α.[x];
		by iff_elim2[OF ab].
	.

interpret iff_iff: MetaCommutative (⟺) (⟺);
	by iff_intro[OF iff.sym iff.sym].

lemma imp_imp_iff: if [P] then (P ⟹ Q) ⟺ Q;
	apply iff_intro,
	- if PQ: P ⟹ Q;
		by PQ.
	.

lemma imp_iff_iff: if [P] then (P ⟺ Q) ⟺ Q;
	apply iff_intro,
	- if PQ: P ⟺ Q;
		by iff_elim1[OF PQ].
	- by iff_intro.
	.

lemma all_imp2_iff: (∀Q. (P ⟹ Q) ⟹ Q) ⟺ P;
	apply iff_intro,
	- if all: ∀Q. (P ⟹ Q) ⟹ Q;
		apply all.
	- if [P];
		- for Q, if PQ: P ⟹ Q;
			by PQ.
		.
	.

lemma imp3_iff: (((P ⟹ Q) ⟹ Q) ⟹ Q) ⟺ (P ⟹ Q);
	apply iff_intro[OF imp2_imp_imp],
	- if PQ: P ⟹ Q, PQQ: (P ⟹ Q) ⟹ Q then Q;
		by PQQ[OF PQ].
	.

lemma imp_all_iff: (P ⟹ ∀x. α.[x]) ⟺ (∀x. P ⟹ α.[x]);
	by iff_intro[OF imp_all all_imp].

lemma imp_iff_iff1: if [P] then (P ⟺ Q) ⟺ Q;
	apply iff_intro,
	- if PQ: P ⟺ Q;
		by iff_elim1[OF PQ].
	by iff_intro.

lemma iff_true: P ⟹ P ⟺ true;
	by iff_intro.

lemma true_imp_iff: (true ⟹ P) ⟺ P;
	by imp_imp_iff[OF true_intro].

lemma imp_true_iff: (P ⟹ true) ⟺ true;
	by iff_intro.

lemma true_iff_iff: (true ⟺ P) ⟺ P;
	apply iff_intro,
	- if P1: true ⟺ P;
		fold P1.
	- if P: P;
		by #unfold iff_true[OF P].
	.

lemma iff_true_iff: (P ⟺ true) ⟺ P;
	unfold[0] iff_iff.commute,
	by true_iff_iff.

lemma imp_refl_iff: (P ⟹ P) ⟺ true;
	by #unfold iff_true_iff.

lemma iff_elim: if PQ: P ⟺ Q then ∀R. ((P ⟹ Q) ⟹ (Q ⟹ P) ⟹ R) ⟹ R;
	- for R;
		unfold+ PQ imp_refl_iff true_imp_iff.
	.

---
### Conjunction
---

interpret and: MetaSymmetric (∧);
	- for P Q, if PQ: P ∧ Q then Q ∧ P;
		by and_intro and_elim2[OF PQ] and_elim1[OF PQ].
	.

lemma and_elim: if PQ: P ∧ Q then ∀R. (P ⟹ Q ⟹ R) ⟹ R;
	- for R, if PQR: P ⟹ Q ⟹ R;
		by PQR and_elim1[OF PQ] and_elim2[OF PQ].
	.

lemma and_iff: P ∧ Q ⟺ (∀R. (P ⟹ Q ⟹ R) ⟹ R);
	apply iff_intro[OF and_elim],
	- if all: ∀R. (P ⟹ Q ⟹ R) ⟹ R;
		apply all,
		by and_intro.
	.

lemma iff_cong_and#cong: for P R, if PQ: P ⟺ Q, RS: R ⟺ S then P ∧ R ⟺ Q ∧ S;
	apply iff_intro,
	- if PR: P ∧ R;
		by and_intro and_elim1[OF PR] and_elim2[OF PR] #fold PQ RS.
	- if QS: Q ∧ S;
		by and_intro and_elim1[OF QS] and_elim2[OF QS] #unfold PQ RS.
	.

interpret and_iff: MetaCommutative (∧) (⟺);
	by iff_intro[OF and.sym and.sym].

interpret and_iff: MetaAssociative (∧) (⟺);
	show: for P Q R, P ∧ Q ∧ R ⟺ P ∧ (Q ∧ R);
		apply iff_intro,
		- if PQR: P ∧ Q ∧ R;
			by and_intro
				and_elim1[OF and_elim1[OF PQR]]
				and_elim2[OF and_elim1[OF PQR]]
				and_elim2[OF PQR].
		- if PQR: P ∧ (Q ∧ R);
			by and_intro
				and_elim1[OF PQR]
				and_elim1[OF and_elim2[OF PQR]]
				and_elim2[OF and_elim2[OF PQR]].
		.
	.

lemma and_imp_iff: (P ∧ Q ⟹ R) ⟺ (P ⟹ Q ⟹ R);
	apply iff_intro,
	- if imp: P ∧ Q ⟹ R, [P, Q] then R;
		by imp and_intro.
	- if imp: P ⟹ Q ⟹ R, and: P ∧ Q then R;
		by imp and_elim1[OF and] and_elim2[OF and].
	.

lemma true_and_iff: true ∧ P ⟺ P;
	apply iff_intro[OF and_elim2],
	by and_intro[OF true_intro].

lemma true_and_true: true ∧ true;
	unfold true_and_iff,
	by true_intro.

lemma and_true_iff: P ∧ true ⟺ P;
	unfold and_iff.commute,
	unfold true_and_iff.

lemma iff_iff_and: (P ⟺ Q) ⟺ (P ⟹ Q) ∧ (Q ⟹ P);
	apply iff_intro,
	- if PQ: P ⟺ Q;
		by and_intro[OF iff_elim1[OF PQ] iff_elim2[OF PQ]].
	- if and: (P ⟹ Q) ∧ (Q ⟹ P);
		by and_elim[OF and iff_intro].
	.

lemma all_and_iff: (∀x. α.[x] ∧ β.[x]) ⟺ (∀x. α.[x]) ∧ (∀x. β.[x]);
	apply iff_intro,
	- if ab: ∀x. α.[x] ∧ β.[x];
		apply and_intro,
		- for x;
			by and_elim1[OF ab].
		- for x;
			by and_elim2[OF ab].
		.
	unfold and_imp_iff,
	- if [∀x. α.[x], ∀x. β.[x]];
		by and_intro.
	.

---
### Negation
---

lemma imp_not: if [P], nQ: ¬Q then ¬(P ⟹ Q);
	apply not_intro,
	- if PQ: P ⟹ Q;
		by not_imp_false[OF nQ] PQ.
	.

lemma imp_not_imp: if PQ: P ⟹ Q, nQ: ¬Q then ¬P;
	apply not_intro,
	by not_imp_false[OF nQ] PQ.

lemma imp_not_sym: if PnQ: P ⟹ ¬Q, [Q] then ¬P;
	apply not_intro,
	- if [P];
		have nQ: ¬Q;
			by PnQ.
		by not_imp_false[OF nQ].
	.

lemma nnot_intro: if [P] then ¬¬P;
	apply not_intro,
	- if nP: ¬P;
		by not_imp_false[OF nP].
	.

lemma not_imp_not_all: if nax: ¬α.[x] then ¬(∀y. α.[y]);
	by not_intro not_imp_false[OF nax].

lemma not_false: ¬false;
	by not_intro[OF imp.refl].

lemma iff_cong_not#cong: if PQ: P ⟺ Q then ¬P ⟺ ¬Q;
	apply iff_intro,
	- if nP: ¬P;
		apply not_intro,
		by not_imp_false[OF nP] iff_elim2[OF PQ].
	- if nQ: ¬Q;
		apply not_intro,
		by not_imp_false[OF nQ] iff_elim1[OF PQ].
	.

lemma not_iff_imp_false: ¬P ⟺ (P ⟹ false);
	by iff_intro[OF not_imp_false not_intro].

lemma imp_not_commute: (P ⟹ ¬Q) ⟺ (Q ⟹ ¬P);
	by iff_intro[OF imp_not_sym imp_not_sym].

lemma nnnot_iff: ¬¬¬P ⟺ ¬P;
	unfold+ not_iff_imp_false,
	by imp3_iff.

lemma nnot_imp_not_iff: (¬¬P ⟹ ¬Q) ⟺ (P ⟹ ¬Q);
	unfold imp_not_commute,
	unfold nnnot_iff.

lemma nnimp_imp_nnot: if nnPQ: ¬¬(P ⟹ Q), [P] then ¬¬Q;
	apply not_intro,
	- if nQ: ¬Q;
		apply+ not_imp_false[OF nnPQ] not_intro,
		- if PQ: P ⟹ Q;
			by not_imp_false[OF nQ] PQ.
		.
	.

lemma nnimp_not_iff: ¬¬(P ⟹ ¬Q) ⟺ (P ⟹ ¬Q);
	apply iff_intro,
	- if nnimp: ¬¬(P ⟹ ¬Q), P: P then ¬Q;
		by nnimp_imp_nnot[OF nnimp P][unfolded nnnot_iff].
	apply nnot_intro=.

lemma not_true_iff: ¬true ⟺ false;
	apply iff_intro,
	- if nt: ¬true;
		by not_imp_false[OF nt].
	by not_intro.

lemma not_false_iff: ¬false ⟺ true;
	by iff_true[OF not_false].

lemma false_imp_false_iff: (false ⟹ false) ⟺ true;
	by iff_true[OF imp.refl].

lemma false_and_false_iff: false ∧ false ⟺ false;
	apply iff_intro[OF and_elim1],
	by and_intro.

lemma nand_intro1: if nP: ¬P then ¬(P ∧ Q);
	apply not_intro,
	- if PQ: P ∧ Q then false;
		by not_imp_false[OF nP and_elim1[OF PQ]].
	.

lemma nand_intro2: if nQ: ¬Q then ¬(P ∧ Q);
	apply not_intro,
	- if PQ: P ∧ Q then false;
		by not_imp_false[OF nQ and_elim2[OF PQ]].
	.

lemma nand_iff_imp_not: ¬(P ∧ Q) ⟺ (P ⟹ ¬Q);
	unfold+ not_iff_imp_false and_imp_iff.

lemma non_contradiction: ¬(P ∧ ¬P);
	unfold nand_iff_imp_not,
	by nnot_intro.

lemma nnot_imp: if imp: ¬¬P ⟹ Q then P ⟹ Q;
	by imp nnot_intro.

lemma nnot_imp_nnot: if nnP: ¬¬P, PQ: P ⟹ Q then ¬¬Q;
	apply not_intro,
	- if [¬Q];
		have! ¬P;
			by imp_not_imp[OF PQ].
		by not_imp_false[OF nnP].
	.

lemma nnot_not_imp_nimp: if nnP: ¬¬P, [¬Q] then ¬(P ⟹ Q);
	apply not_intro,
	- if PQ: P ⟹ Q;
		have nnQ: ¬¬Q;
			by nnot_imp_nnot[OF nnP PQ].
		by not_imp_false[OF nnQ].
	.

lemma nand_nnot_iff: ¬(P ∧ ¬¬Q) ⟺ ¬(P ∧ Q);
	unfold+ nand_iff_imp_not,
	unfold nnnot_iff.

lemma nnot_nand_iff: ¬(¬¬P ∧ Q) ⟺ ¬(P ∧ Q);
	unfold and_iff.commute,
	unfold nand_nnot_iff,
	unfold and_iff.commute.

lemma raw_or_imp_iff: ((∀S. (P ⟹ S) ⟹ (Q ⟹ S) ⟹ S) ⟹ R) ⟺ (P ⟹ R) ∧ (Q ⟹ R);
	apply iff_intro,
	- if or_imp: (∀S. (P ⟹ S) ⟹ (Q ⟹ S) ⟹ S) ⟹ R;
		apply and_intro,
		- if [P];
			apply or_imp,
			- for S, if PS: P ⟹ S, QS: Q ⟹ S then S;
				by PS.
			.
		- if [Q];
			apply or_imp,
			- for S, if PS: P ⟹ S, QS: Q ⟹ S then S;
				by QS.
			.
		.
	- if and: (P ⟹ R) ∧ (Q ⟹ R), or: (∀S. (P ⟹ S) ⟹ (Q ⟹ S) ⟹ S);
		by or[OF and_elim1[OF and] and_elim2[OF and]].
	.

lemma raw_nor_iff_and: ¬(∀R. (P ⟹ R) ⟹ (Q ⟹ R) ⟹ R) ⟺ ¬P ∧ ¬Q;
	unfold+ not_iff_imp_false,
	by raw_or_imp_iff.

lemma nnand_iff: ¬¬(P ∧ Q) ⟺ ¬¬P ∧ ¬¬Q;
	fold nnot_nand_iff,
	fold nand_nnot_iff,
	fold raw_nor_iff_and,
	unfold nnnot_iff,
	unfold raw_nor_iff_and.

---
### Disjunction
---

lemma or_intro: if assm: ∀R. (P ⟹ R) ⟹ (Q ⟹ R) ⟹ R then P ∨ Q;
	by assm[OF or_intro1 or_intro2].

interpret or: MetaSymmetric (∨);
	- for P Q, if PQ: P ∨ Q then Q ∨ P;
		by or_elim[OF PQ or_intro2 or_intro1].
	.

lemma iff_cong_or#cong: for P R, if PQ: P ⟺ Q, RS: R ⟺ S then P ∨ R ⟺ Q ∨ S;
	apply iff_intro,
	- if PR: P ∨ R;
		apply or_elim[OF PR],
		- by or_intro1 iff_elim1[OF PQ].
		- by or_intro2 iff_elim1[OF RS].
		.
	- if QS: Q ∨ S;
		apply or_elim[OF QS],
		- by or_intro1 iff_elim2[OF PQ].
		- by or_intro2 iff_elim2[OF RS].
		.
	.

interpret or: MetaSymmetric (∨);
	- for P Q, if or: P ∨ Q then Q ∨ P;
		apply or_elim[OF or],
		- by or_intro2.
		- by or_intro1.
		.
	.

interpret or_iff: MetaCommutative (∨) (⟺);
	show: for P Q, P ∨ Q ⟺ Q ∨ P;
		apply iff_intro,
		- if PQ: P ∨ Q;
			by or.sym[OF PQ].
		- if QP: Q ∨ P;
			by or.sym[OF QP].
		.
	.

interpret or_iff: MetaAssociative (∨) (⟺);
	show: for P Q R, P ∨ Q ∨ R ⟺ P ∨ (Q ∨ R);
		apply iff_intro,
		- if PQR: P ∨ Q ∨ R;
			apply or_elim[OF PQR],
			- if PQ: P ∨ Q;
				apply or_elim[OF PQ],
				- by or_intro1.
				- if [Q];
					apply or_intro2,
					apply or_intro1.
				.
			- if [R];
				apply or_intro2,
				apply or_intro2.
			.
		- if PQR: P ∨ (Q ∨ R);
			apply or_elim[OF PQR],
			- if [P];
				apply or_intro1,
				apply or_intro1.
			- if QR: Q ∨ R;
				apply or_elim[OF QR],
				- if [Q];
					apply or_intro1,
					apply or_intro2.
				by or_intro2.
			.
		.
	.

lemma imp_or_if: if or: (P ⟹ Q) ∨ (P ⟹ R), [P] then Q ∨ R;
	by or[unfolded imp_imp_iff].

lemma or_imp_iff: (P ∨ Q ⟹ R) ⟺ (P ⟹ R) ∧ (Q ⟹ R);
	apply iff_intro,
	- if nor: P ∨ Q ⟹ R;
		apply and_intro,
		- by nor or_intro1.
		- by nor or_intro2.
		.
	- if and: (P ⟹ R) ∧ (Q ⟹ R), or: P ∨ Q;
		apply or_elim[OF or],
		- by and_elim1[OF and].
		- by and_elim2[OF and].
		.
	.

lemma nor_iff: ¬(P ∨ Q) ⟺ ¬P ∧ ¬Q;
	unfold+ not_iff_imp_false,
	by or_imp_iff.

lemma nnot_nor_iff: ¬(¬¬P ∨ Q) ⟺ ¬(P ∨ Q);
	unfold+ nor_iff nnnot_iff.

lemma nor_nnot_iff: ¬(P ∨ ¬¬Q) ⟺ ¬(P ∨ Q);
	unfold+ nor_iff nnnot_iff.

lemma nnot_excluded_middle: ¬¬(P ∨ ¬P);
	unfold nor_iff,
	by non_contradiction.

lemma or_imp_nand: if PQ: P ∨ Q then ¬(¬P ∧ ¬Q);
	apply not_intro,
	- if and: ¬P ∧ ¬Q;
		have nP: ¬P;
			by and_elim1[OF and].
		have nQ: ¬Q;
			by and_elim2[OF and].
		apply or_elim[OF PQ],
		- by not_imp_false[OF nP].
		- by not_imp_false[OF nQ].
		.
	.

lemma false_or_false_iff: false ∨ false ⟺ false;
	apply iff_intro,
	- if or: false ∨ false then false;
		apply or_elim[OF or].
	by or_intro1.

lemma true_or: true ∨ P;
	by or_intro1[OF true_intro].

lemma or_true: P ∨ true;
	by or_intro2[OF true_intro].


---
### Existence
---

lemma ex_intro: if assm: ∀P. (∀x. α.[x] ⟹ P) ⟹ P then ∃x. α.[x];
	apply assm,
	- for x;
		apply ex_intro1=.
	.

lemma ex_iff: (∃x. α.[x]) ⟺ (∀P. (∀x. α.[x] ⟹ P) ⟹ P);
	by iff_intro[OF ex_elim ex_intro].

lemma ex_imp_all_imp: if ex: ∃x. α.[x] ⟹ P, [∀x. α.[x]] then P;
	apply ex_elim[OF ex],
	- for x, if imp: α.[x] ⟹ P;
		by imp.
	.

lemma all_imp_iff_ex: (∀x. α.[x] ⟹ P) ⟺ (∃x. α.[x]) ⟹ P;
	apply iff_intro,
	- if imp: ∀x. α.[x] ⟹ P, ex: ∃x. α.[x];
		obtain x where ax: α.[x];
			- for P; apply ex[unfolded ex_iff](P)=.
			.
		by imp[OF ax].
	- if imp: (∃x. α.[x]) ⟹ P;
		- for x, if ax: α.[x];
			by imp ex_intro1[OF ax].
		.
	.


---
## Double negation and universal quantification.

The following direction is provable in general, but the opposite direction requires something similar to the axiom of choice.
---
lemma nnall_imp: if nnall: ¬¬(∀x. α.[x]) then (∀x. ¬¬α.[x]);
	- for x;
		apply not_intro,
		- if nax: ¬α.[x];
			by not_imp_false[OF nnall] not_imp_not_all[OF nax].
		.
	.

---
The other direction is provable if inside the quantification has negation.
---

lemma nex_iff_all_not: ¬(∃x. α.[x]) ⟺ (∀x. ¬α.[x]);
	unfold+ not_iff_imp_false,
	fold all_imp_iff_ex.

lemma nnall_not_iff: ¬¬(∀x. ¬α.[x]) ⟺ (∀x. ¬α.[x]);
	fold+ nex_iff_all_not,
	by nnnot_iff.


