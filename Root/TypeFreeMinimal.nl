-------
# Type-Free Minimal Logic
-------

base Root;

import True;

fix false;

fix (∧);
assume and_intro: P ⟹ Q ⟹ P ∧ Q;
assume and_elim1: P ∧ Q ⟹ P;
assume and_elim2: P ∧ Q ⟹ Q;

fix (¬);
assume not_imp_false: ¬ P ⟹ P ⟹ false;
assume not_intro: (P ⟹ false) ⟹ ¬ P;

fix (⟺);
assume iff_intro: (P ⟹ Q) ⟹ (Q ⟹ P) ⟹ P ⟺ Q;
assume iff_elim1: (P ⟺ Q) ⟹ P ⟹ Q;
assume iff_elim2: (P ⟺ Q) ⟹ Q ⟹ P;

fix (∨);
assume or_intro1: P ⟹ P ∨ Q;
assume or_intro2: Q ⟹ P ∨ Q;
assume or_elim: P ∨ Q ⟹ (P ⟹ R) ⟹ (Q ⟹ R) ⟹ R;

fix (∃);
assume ex_intro1: ∀x α. α.[x] ⟹ ∃x. α.[x];
assume ex_elim: (∃x. α.[x]) ⟹ (∀x. α.[x] ⟹ P) ⟹ P;

finalize;

---
## Theorems

### If-and-only-if
---

interpret iff: MetaEquivalence (⟺) :=
	- if PQ: P ⟺ Q then Q ⟺ P :=
		by iff_intro[OF iff_elim2[OF PQ] iff_elim1[OF PQ]];
	- P ⟺ P :=
		by iff_intro[OF imp.refl imp.refl];
	- if PQ: P ⟺ Q, QR: Q ⟺ R then P ⟺ R :=
		note PR: imp.trans[OF iff_elim1[OF PQ] iff_elim1[OF QR]];
		note RP: imp.trans[OF iff_elim2[OF QR] iff_elim2[OF PQ]];
		by iff_intro[OF PR RP];
	done;
note #concl: iff.refl;

show iff_cong_imp: if PQ: P ⟺ Q, RS: R ⟺ S then (P ⟹ R) ⟺ (Q ⟹ S) :=
	apply iff_intro;
	- if PR: P ⟹ R, [Q] then S :=
		by iff_elim1[OF RS] PR iff_elim2[OF PQ];
	- if QS: Q ⟹ S, [P] then R :=
		by iff_elim2[OF RS] QS iff_elim1[OF PQ];
	done;

show iff_cong_iff: if PQ: P ⟺ Q, RS: R ⟺ S then (P ⟺ R) ⟺ (Q ⟺ S) :=
	apply iff_intro;
	- if PR: P ⟺ R then Q ⟺ S :=
		show QR: Q ⟺ R :=
			by iff.trans[OF iff.sym[OF PQ] PR];
		by iff.trans[OF QR RS];
	- if QS: Q ⟺ S then P ⟺ R :=
		show PS: P ⟺ S :=
			by iff.trans[OF PQ QS];
		by iff.trans[OF PS iff.sym[OF RS]];
	done;

show iff_cong_all: if ab: ∀x. α.[x] ⟺ β.[x] then (∀x. α.[x]) ⟺ (∀x. β.[x]) :=
	apply iff_intro;
	- if [∀x. α.[x]] then ∀x. β.[x] :=
		by iff_elim1[OF ab];
	- if [∀x. β.[x]] then ∀x. α.[x] :=
		by iff_elim2[OF ab];
	done;

setup rewrite iff_elim1 iff_elim2 iff.refl iff.trans;
setup dual iff.sym;
setup cong iff_cong_imp iff_cong_iff iff_cong_all;

interpret iff_iff: MetaCommutative (⟺) (⟺) :=
	- (P ⟺ Q) ⟺ (Q ⟺ P) :=
		by iff_intro[OF iff.sym iff.sym];
	done;

show imp_imp_iff: if [P] then (P ⟹ Q) ⟺ Q :=
	apply iff_intro;
	- if PQ: P ⟹ Q :=
		by PQ;
	done;

show imp_iff_iff: if [P] then (P ⟺ Q) ⟺ Q :=
	apply iff_intro;
	- if PQ: P ⟺ Q :=
		by iff_elim1[OF PQ];
	- := by iff_intro;
	done;

show all_imp2_iff: (∀Q. (P ⟹ Q) ⟹ Q) ⟺ P :=
	apply iff_intro;
	- if all: ∀Q. (P ⟹ Q) ⟹ Q :=
		apply all;
		done;
	- if [P] :=
		- for Q, if PQ: P ⟹ Q :=
			by PQ;
		done;
	done;

show imp3_iff: (((P ⟹ Q) ⟹ Q) ⟹ Q) ⟺ (P ⟹ Q) :=
	apply iff_intro;
	- := just imp2_imp_imp;
	- if PQ: P ⟹ Q, PQQ: (P ⟹ Q) ⟹ Q then Q :=
		by PQQ[OF PQ];
	done;

show imp_all_iff: (P ⟹ ∀x. α.[x]) ⟺ (∀x. P ⟹ α.[x]) :=
	by iff_intro[OF imp_all all_imp];

show imp_iff_iff1: if [P] then (P ⟺ Q) ⟺ Q :=
	apply iff_intro;
	- if PQ: P ⟺ Q :=
		by iff_elim1[OF PQ];
	- if [Q] :=
		by iff_intro;
	done;

show iff_true: if [P] then P ⟺ true :=
	by iff_intro;

show true_imp_iff: (true ⟹ P) ⟺ P :=
	by imp_imp_iff[OF true_intro];

show imp_true_iff: (P ⟹ true) ⟺ true :=
	by iff_intro;

show true_iff_iff: (true ⟺ P) ⟺ P :=
	apply iff_intro;
	- if P1: true ⟺ P :=
		fold P1;
		done;
	- if P: P :=
		unfold iff_true[OF P];
		done;
	done;

show iff_true_iff: (P ⟺ true) ⟺ P :=
	unfold[0] iff_iff.commute;
	by true_iff_iff(P);

---
### Conjunction
---

interpret and: MetaSymmetric (∧) :=
	- if PQ: P ∧ Q then Q ∧ P :=
		by and_intro and_elim2[OF PQ] and_elim1[OF PQ];
	done;

show and_elim: if PQ: P ∧ Q then ∀R. (P ⟹ Q ⟹ R) ⟹ R :=
	- for R, if PQR: P ⟹ Q ⟹ R :=
		by PQR and_elim1[OF PQ] and_elim2[OF PQ];
	done;

show and_iff: P ∧ Q ⟺ (∀R. (P ⟹ Q ⟹ R) ⟹ R) :=
	apply iff_intro;
	- := just and_elim;
	- if all: ∀R. (P ⟹ Q ⟹ R) ⟹ R :=
		apply all;
		by and_intro;
	done;

show iff_cong_and: if PQ: P ⟺ Q, RS: R ⟺ S then P ∧ R ⟺ Q ∧ S :=
	apply iff_intro;
	- if PR: P ∧ R :=
		apply and_intro;
		- :=
			by iff_elim1[OF PQ] and_elim1[OF PR];
		- :=
			by iff_elim1[OF RS] and_elim2[OF PR];
		done;
	- if QS: Q ∧ S :=
		apply and_intro;
		- :=
			by iff_elim2[OF PQ] and_elim1[OF QS];
		- :=
			by iff_elim2[OF RS] and_elim2[OF QS];
		done;
	done;

setup cong iff_cong_and;

interpret and_iff: MetaCommutative (∧) (⟺) :=
	- P ∧ Q ⟺ Q ∧ P :=
		by iff_intro[OF and.sym and.sym];
	done;

interpret and_iff: MetaAssociative (∧) (⟺) :=
	- P ∧ Q ∧ R ⟺ P ∧ (Q ∧ R) :=
		apply iff_intro;
		- if PQR: P ∧ Q ∧ R :=
			note! and_elim1[OF and_elim1[OF PQR]];
			note! and_elim2[OF and_elim1[OF PQR]];
			note! and_elim2[OF PQR];
			by and_intro;
		- if PQR: P ∧ (Q ∧ R) :=
			apply and_intro;
			apply and_intro;
			show! P :=
				by and_elim1[OF PQR];
			show! Q :=
				by and_elim1[OF and_elim2[OF PQR]];
			show! R :=
				by and_elim2[OF and_elim2[OF PQR]];
			done;
		done;
	done;

show and_imp_iff: (P ∧ Q ⟹ R) ⟺ (P ⟹ Q ⟹ R) :=
	apply iff_intro;
	- if imp: P ∧ Q ⟹ R, [P, Q] then R :=
		by imp and_intro;
	- if imp: P ⟹ Q ⟹ R, and: P ∧ Q then R :=
		by imp and_elim1[OF and] and_elim2[OF and];
	done;

show true_and_iff: true ∧ P ⟺ P :=
	apply iff_intro;
	- := just and_elim2;
	by and_intro[OF true_intro];

show true_and_true: true ∧ true :=
	unfold true_and_iff;
	by true_intro;

show and_true_iff: P ∧ true ⟺ P :=
	unfold and_iff.commute;
	unfold true_and_iff;
	done;

show iff_iff_and: (P ⟺ Q) ⟺ (P ⟹ Q) ∧ (Q ⟹ P) :=
	apply iff_intro;
	- if PQ: P ⟺ Q :=
		apply and_intro;
		just iff_elim1[OF PQ] iff_elim2[OF PQ];
	- if and: (P ⟹ Q) ∧ (Q ⟹ P) :=
		apply and_elim[OF and];
		just iff_intro;
	done;

---
### Negation
---

show imp_not: if [P], nQ: ¬Q then ¬(P ⟹ Q) :=
	apply not_intro;
	- if PQ: P ⟹ Q :=
		by not_imp_false[OF nQ] PQ;
	done;

show imp_not_imp: if PQ: P ⟹ Q, nQ: ¬Q then ¬P :=
	apply not_intro;
	by not_imp_false[OF nQ] PQ;

show imp_not_sym: if PnQ: P ⟹ ¬Q, [Q] then ¬P :=
	apply not_intro;
	- if [P] :=
		show nQ: ¬Q :=
			by PnQ;
		by not_imp_false[OF nQ];
	done;

show not_imp_not_all: if nax: ¬α.[x] then ¬(∀y. α.[y]) :=
	by not_intro not_imp_false[OF nax];

show not_false: ¬false :=
	by not_intro[OF imp.refl];

show iff_cong_not: if PQ: P ⟺ Q then ¬P ⟺ ¬Q :=
	apply iff_intro;
	- if nP: ¬P :=
		apply not_intro;
		by not_imp_false[OF nP] iff_elim2[OF PQ];
	- if nQ: ¬Q :=
		apply not_intro;
		by not_imp_false[OF nQ] iff_elim1[OF PQ];
	done;

setup cong iff_cong_not;

show not_iff_imp_false: ¬P ⟺ (P ⟹ false) :=
	by iff_intro[OF not_imp_false not_intro];

show imp_not_commute: (P ⟹ ¬Q) ⟺ (Q ⟹ ¬P) :=
	apply iff_intro;
	just imp_not_sym;

show not_true_iff: ¬true ⟺ false :=
	apply iff_intro;
	- if nt: ¬true :=
		by not_imp_false[OF nt];
	by not_intro;

show not_false_iff: ¬false ⟺ true :=
	by iff_true[OF not_false];

show false_and_false_iff: false ∧ false ⟺ false :=
	apply iff_intro;
	- := just and_elim1;
	- := by and_intro;
	done;

show false_imp_false_iff: (false ⟹ false) ⟺ true :=
	by iff_true[OF imp.refl];

show nand_intro1: if nP: ¬P then ¬(P ∧ Q) :=
	apply not_intro;
	- if PQ: P ∧ Q then false :=
		by not_imp_false[OF nP and_elim1[OF PQ]];
	done;

show nand_intro2: if nQ: ¬Q then ¬(P ∧ Q) :=
	apply not_intro;
	- if PQ: P ∧ Q then false :=
		by not_imp_false[OF nQ and_elim2[OF PQ]];
	done;

show nand_iff_imp_not: ¬(P ∧ Q) ⟺ (P ⟹ ¬Q) :=
	unfold+ not_iff_imp_false and_imp_iff;
	done;

show nnot_intro: if [P] then ¬¬P :=
	apply not_intro;
	- if nP: ¬P :=
		by not_imp_false[OF nP];
	done;

show nnot_imp: if imp: ¬¬P ⟹ Q, [P] then Q :=
	by imp nnot_intro;

show nnot_imp_nnot: if nnP: ¬¬P, PQ: P ⟹ Q then ¬¬Q :=
	apply not_intro;
	- if [¬Q] :=
		show! ¬P :=
			by imp_not_imp[OF PQ];
		by not_imp_false[OF nnP];
	done;

show nnimp_imp_nnot: if nnPQ: ¬¬(P ⟹ Q), [P] then ¬¬Q :=
	apply not_intro;
	- if nQ: ¬Q :=
		apply+ not_imp_false[OF nnPQ] not_intro;
		- if PQ: P ⟹ Q :=
			by not_imp_false[OF nQ] PQ;
		done;
	done;

show nnot_not_imp_nimp: if nnP: ¬¬P, [¬Q] then ¬(P ⟹ Q) :=
	apply not_intro;
	- if PQ: P ⟹ Q :=
		show nnQ: ¬¬Q :=
			by nnot_imp_nnot[OF nnP PQ];
		by not_imp_false[OF nnQ];
	done;

show nnnot_iff: ¬¬¬P ⟺ ¬P :=
	unfold+ not_iff_imp_false;
	by imp3_iff;

show non_contradiction: ¬(P ∧ ¬P) :=
	unfold nand_iff_imp_not;
	by nnot_intro;

---
### Disjunction
---

show or_intro: if assm: ∀R. (P ⟹ R) ⟹ (Q ⟹ R) ⟹ R then P ∨ Q :=
	by assm[OF or_intro1 or_intro2];

interpret or: MetaSymmetric (∨) :=
	- if PQ: P ∨ Q then Q ∨ P :=
		by or_elim[OF PQ or_intro2 or_intro1];
	done;

show iff_cong_or: if PQ: P ⟺ Q, RS: R ⟺ S then P ∨ R ⟺ Q ∨ S :=
	apply iff_intro;
	- if PR: P ∨ R :=
		apply or_elim[OF PR];
		- := by or_intro1 iff_elim1[OF PQ];
		- := by or_intro2 iff_elim1[OF RS];
		done;
	- if QS: Q ∨ S :=
		apply or_elim[OF QS];
		- := by or_intro1 iff_elim2[OF PQ];
		- := by or_intro2 iff_elim2[OF RS];
		done;
	done;

setup cong iff_cong_or;

--### Existence

show ex_intro: if assm: ∀P. (∀x. α.[x] ⟹ P) ⟹ P then ∃x. α.[x] :=
	apply assm;
	- for x :=
		just ex_intro1;
	done;

show ex_imp_all_imp: if ex: ∃x. α.[x] ⟹ P, [∀x. α.[x]] then P :=
	apply ex_elim[OF ex];
	- for x, if imp: α.[x] ⟹ P :=
		by imp;
	done;

show raw_or_imp_iff: ((∀S. (P ⟹ S) ⟹ (Q ⟹ S) ⟹ S) ⟹ R) ⟺ (P ⟹ R) ∧ (Q ⟹ R) :=
	apply iff_intro;
	- if or_imp: (∀S. (P ⟹ S) ⟹ (Q ⟹ S) ⟹ S) ⟹ R :=
		apply and_intro;
		- if [P] :=
			apply or_imp;
			- for S, if PS: P ⟹ S, QS: Q ⟹ S then S :=
				by PS;
			done;
		- if [Q] :=
			apply or_imp;
			- for S, if PS: P ⟹ S, QS: Q ⟹ S then S :=
				by QS;
			done;
		done;
	- if and: (P ⟹ R) ∧ (Q ⟹ R), or: (∀S. (P ⟹ S) ⟹ (Q ⟹ S) ⟹ S) :=
		apply or;
		just and_elim1[OF and] and_elim2[OF and];
	done;

show all_and_iff: (∀x. α.[x] ∧ β.[x]) ⟺ (∀x. α.[x]) ∧ (∀x. β.[x]) :=
	apply iff_intro;
	- if ab: ∀x. α.[x] ∧ β.[x] :=
		apply and_intro;
		- for x :=
			by and_elim1[OF ab];
		- for x :=
			by and_elim2[OF ab];
		done;
	unfold and_imp_iff;
	- if [∀x. α.[x], ∀x. β.[x]] :=
		by and_intro;
	done;

show all_imp_iff_raw_ex: (∀x. α.[x] ⟹ P) ⟺ (∀Q. (∀x. α.[x] ⟹ Q) ⟹ Q) ⟹ P :=
	apply iff_intro;
	- if imp: ∀x. α.[x] ⟹ P, ex: ∀Q. (∀x. α.[x] ⟹ Q) ⟹ Q :=
		obtain x where ax: α.[x] :=
			- for P := just ex;
			done;
		by imp[OF ax];
	- if imp: (∀Q. (∀x. α.[x] ⟹ Q) ⟹ Q) ⟹ P :=
		- for x, if ax: α.[x] :=
			apply imp;
			- for Q, if all: ∀x. α.[x] ⟹ Q :=
				by all[OF ax];
			done;
		done;
	done;


---
## Double negation and conjunction.
---

show nnot_imp_not_iff: (¬¬P ⟹ ¬Q) ⟺ (P ⟹ ¬Q) :=
	unfold imp_not_commute;
	unfold nnnot_iff;
	done;

show nnimp_not_iff: ¬¬(P ⟹ ¬Q) ⟺ (P ⟹ ¬Q) :=
	apply iff_intro;
	- if nnimp: ¬¬(P ⟹ ¬Q), P: P then ¬Q :=
		by nnimp_imp_nnot[OF nnimp P][unfolded nnnot_iff];
	just nnot_intro;

show nand_nnot_iff: ¬(P ∧ ¬¬Q) ⟺ ¬(P ∧ Q) :=
	unfold+ nand_iff_imp_not;
	unfold nnnot_iff;
	done;

show nnot_nand_iff: ¬(¬¬P ∧ Q) ⟺ ¬(P ∧ Q) :=
	unfold and_iff.commute;
	unfold nand_nnot_iff;
	unfold and_iff.commute;
	done;

show raw_nor_iff_and: ¬(∀R. (P ⟹ R) ⟹ (Q ⟹ R) ⟹ R) ⟺ ¬P ∧ ¬Q :=
	unfold+ not_iff_imp_false;
	by raw_or_imp_iff;

show nnand_iff: ¬¬(P ∧ Q) ⟺ ¬¬P ∧ ¬¬Q :=
	fold nnot_nand_iff;
	fold nand_nnot_iff;
	fold raw_nor_iff_and;
	unfold nnnot_iff;
	unfold raw_nor_iff_and;
	done;

---
## Double negation and universal quantification.

The following direction is provable in general, but the opposite direction requires something similar to the axiom of choice.
---
show nnall_imp: if nnall: ¬¬(∀x. α.[x]) then (∀x. ¬¬α.[x]) :=
	- for x :=
		apply not_intro;
		- if nax: ¬α.[x] :=
			by not_imp_false[OF nnall] not_imp_not_all[OF nax];
		done;
	done;

---
The other direction is provable if inside the quantification has negation.
---

show raw_nex_iff_all_not: ¬(∀P. (∀x. α.[x] ⟹ P) ⟹ P) ⟺ (∀x. ¬α.[x]) :=
	unfold+ not_iff_imp_false;
	fold all_imp_iff_raw_ex;
	done;

show nnall_not_iff: ¬¬(∀x. ¬α.[x]) ⟺ (∀x. ¬α.[x]) :=
	fold+ raw_nex_iff_all_not;
	by nnnot_iff;


