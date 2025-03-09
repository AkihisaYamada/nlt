---
# Minimal Propositional Logic
---

base Root;

---
## Axiomatization
---

fix prop; -- We axiomatize what expressions are propositions.

fix true;
import true: Member prop true;
assume true_intro! true;

fix false;
import false: Member prop false;
--Minimal Logic only asserts that false is a proposition.

import imp: Magma prop (⟹);

fix (¬);
import not: Unary prop (¬);
assume not_intro: (P ⟹ false) ⟹ prop P ⟹ ¬ P;
assume not_imp_false: ¬ P ⟹ P ⟹ prop P ⟹ false;

fix (∧);
import and: Magma prop (∧);
assume and_intro: P ⟹ Q ⟹ prop P ⟹ prop Q ⟹ P ∧ Q;
assume and_elim1: P ∧ Q ⟹ prop P ⟹ prop Q ⟹ P;
assume and_elim2: P ∧ Q ⟹ prop P ⟹ prop Q ⟹ Q;

fix (⟺);
import iff: Magma prop (⟺);
assume iff_intro: (P ⟹ Q) ⟹ (Q ⟹ P) ⟹ prop P ⟹ prop Q ⟹ (P ⟺ Q);
assume iff_elim1: (P ⟺ Q) ⟹ P ⟹ prop P ⟹ prop Q ⟹ Q;
assume iff_elim2: (P ⟺ Q) ⟹ Q ⟹ prop P ⟹ prop Q ⟹ P;

fix (∨);
import or: Magma prop (∨);
assume or_intro1: P ⟹ prop P ⟹ prop Q ⟹ P ∨ Q;
assume or_intro2: for P Q, Q ⟹ prop P ⟹ prop Q ⟹ P ∨ Q;
assume or_elim: P ∨ Q ⟹ ∀R. (P ⟹ R) ⟹ (Q ⟹ R) ⟹ prop P ⟹ prop Q ⟹ prop R ⟹ R;

begin

note ! imp.type;
note ! true.type;
note ! false.type;
note ! not.type;
note ! iff.type;
note ! and.type;
note ! or.type;

ctxt;

---
## Theorems
---

interpret iff: Reflexive prop (⟺) :=
	- by iff_intro;
	done;

note ! iff.refl;

interpret iff: Symmetric prop (⟺) :=
	- for P Q, if PQ: P ⟺ Q, [prop P, prop Q] then Q ⟺ P :=
		apply iff_intro;
		- by iff_elim2[OF PQ];
		by iff_elim1[OF PQ];
	done;

interpret iff: Transitive prop (⟺) :=
	- for P Q R, if PQ: P ⟺ Q, QR: Q ⟺ R, [prop P, prop Q, prop R] then P ⟺ R :=
		apply iff_intro;
		- by iff_elim1[OF QR] iff_elim1[OF PQ];
		by iff_elim2[OF PQ] iff_elim2[OF QR];
	done;

lemma iff_imp: if PQ: P ⟺ Q, [prop P, prop Q] then P ⟹ Q :=
	by iff_elim1[OF PQ];

lemma iff_imp_rev: if PQ: P ⟺ Q, [prop P, prop Q] then Q ⟹ P :=
	by iff_elim2[OF PQ];

setup rewrite iff_imp iff_imp_rev iff.refl iff.trans;
setup dual iff.sym;

lemma iff_cong_imp#cong: for P R,
	if PQ: P ⟺ Q, RS: R ⟺ S, [prop P, prop Q, prop R, prop S]
	then (P ⟹ R) ⟺ (Q ⟹ S)
:=
	apply iff_intro;
	- if PR: P ⟹ R :=
		by PR #fold RS PQ-;
	- if QS: Q ⟹ S :=
		by QS #unfold RS PQ-;
	done;

lemma iff_cong_iff#cong: for P R,
	if PQ: P ⟺ Q, RS: R ⟺ S, [prop P, prop Q, prop R, prop S]
	then (P ⟺ R) ⟺ (Q ⟺ S)
:=
	apply iff_intro;
	- if PR: P ⟺ R :=
		apply iff_intro;
		- by #fold RS PR PQ-;
		- by #fold PQ PR- RS-;
		done;
	- if QS: Q ⟺ S :=
		apply iff_intro;
		- by #unfold RS QS- PQ-;
		- by #unfold PQ QS RS-;
		done;
	done;

lemma imp_imp_iff: if [P, prop P, prop Q] then (P ⟹ Q) ⟺ Q :=
	apply iff_intro;
	- if PQ: P ⟹ Q :=
		by PQ;
	done;

lemma imp_iff_iff: if [P, prop P, prop Q] then (P ⟺ Q) ⟺ Q :=
	apply iff_intro;
	- if PQ: P ⟺ Q :=
		by iff_elim1[OF PQ];
	by iff_intro;

lemma imp3_iff: if [prop P, prop Q] then (((P ⟹ Q) ⟹ Q) ⟹ Q) ⟺ (P ⟹ Q) :=
	apply iff_intro;
	- just imp2_imp_imp;
	- if PQ: P ⟹ Q, PQQ: (P ⟹ Q) ⟹ Q then Q :=
		by PQQ[OF PQ];
	done;

lemma imp_iff_iff1: if [P, prop P, prop Q] then (P ⟺ Q) ⟺ Q :=
	apply iff_intro;
	- if PQ: P ⟺ Q :=
		by iff_elim1[OF PQ];
	- if [Q] :=
		by iff_intro;
	done;

----
### True, False, and Negation
----

lemma iff_true: if [P, prop P] then P ⟺ true :=
	by iff_intro;

lemma true_imp_iff: if [prop P] then (true ⟹ P) ⟺ P :=
	by imp_imp_iff;

lemma imp_true_iff: if [prop P] then (P ⟹ true) ⟺ true :=
	by iff_intro;

lemma iff_cong_not#cong: for P,
	if PQ: P ⟺ Q, [prop P, prop Q] then ¬P ⟺ ¬Q
:=
	apply iff_intro;
	- if nP: ¬P :=
		apply not_intro;
		by not_imp_false[OF nP] iff_elim2[OF PQ];
	- if nQ: ¬Q :=
		apply not_intro;
		by not_imp_false[OF nQ] iff_elim1[OF PQ];
	done;

lemma not_iff_imp_false: if [prop P] then ¬P ⟺ (P ⟹ false) :=
	apply iff_intro;
	- if nP: ¬P :=
		by not_imp_false[OF nP];
	- if Pf: P ⟹ false :=
		by not_intro Pf;
	done;

lemma not_false: ¬false :=
	apply not_intro;
	done;

lemma not_true_iff: ¬true ⟺ false :=
	apply iff_intro;
	- if nt: ¬true :=
		by not_imp_false[OF nt];
	by not_intro;

lemma not_false_iff: ¬false ⟺ true :=
	by iff_true[OF not_false];

lemma nnot_intro: if [P, prop P] then ¬¬P :=
	apply not_intro;
	- if nP: ¬P :=
		by not_imp_false[OF nP];
	done;

lemma nnot_imp: if imp: ¬¬P ⟹ Q, [P, prop P] then Q :=
	by imp nnot_intro;

lemma imp_not: if [P], nQ: ¬Q, [prop P, prop Q] then ¬(P ⟹ Q) :=
	apply not_intro;
	- if PQ: P ⟹ Q :=
		by not_imp_false[OF nQ] PQ;
	done;

lemma imp_not_imp: if PQ: P ⟹ Q, nQ: ¬Q, [prop P, prop Q] then ¬P :=
	apply not_intro;
	by not_imp_false[OF nQ] PQ;

lemma imp_not_sym: if PnQ: P ⟹ ¬Q, [Q, prop P, prop Q] then ¬P :=
	apply not_intro;
	- if [P] :=
		have nQ: ¬Q :=
			by PnQ;
		by not_imp_false[OF nQ];
	done;

lemma nnot_imp_nnot: if nnP: ¬¬P, PQ: P ⟹ Q, [prop P, prop Q] then ¬¬Q :=
	apply not_intro;
	- if nQ: ¬Q :=
		have nP: ¬P :=
			by imp_not_imp[OF PQ nQ];
		by not_imp_false[OF nnP] nP;
	done;

lemma nnimp_imp_nnot: if nnPQ: ¬¬(P ⟹ Q), [P, prop P, prop Q] then ¬¬Q :=
	apply not_intro;
	- if nQ: ¬Q :=
		apply+ not_imp_false[OF nnPQ] not_intro;
		- if PQ: P ⟹ Q :=
			by not_imp_false[OF nQ] PQ;
		done;
	done;

lemma nnot_not_imp_nimp: if nnP: ¬¬P, nQ: ¬Q, [prop P, prop Q] then ¬(P ⟹ Q) :=
	apply not_intro;
	- if PQ: P ⟹ Q :=
		have nnQ: ¬¬Q :=
			by nnot_imp_nnot[OF nnP] PQ;
		by not_imp_false[OF nnQ nQ];
	done;

lemma nnnot_iff: if [prop P] then ¬¬¬P ⟺ ¬P :=
thm not_iff_imp_false;
thms #intro;
thms #exact;
thms #concl;
	unfold+ not_iff_imp_false;
	by imp3_iff;

lemma imp_not_commute: if [prop P, prop Q] then
	(P ⟹ ¬Q) ⟺ (Q ⟹ ¬P)
:=	by iff_intro #elim imp_not_sym;

lemma nnot_imp_not_iff: if [prop P, prop Q] then
	(¬¬P ⟹ ¬Q) ⟺ (P ⟹ ¬Q)
:=	unfold imp_not_commute;
	by #unfold nnnot_iff;

lemma nnimp_not_iff: if [prop P, prop Q] then
	¬¬(P ⟹ ¬Q) ⟺ (P ⟹ ¬Q)
:=	apply iff_intro;
	- if nnimp: ¬¬(P ⟹ ¬Q), P: P then ¬Q :=
		fold nnnot_iff;
		by nnimp_imp_nnot[OF nnimp P];
	by nnot_intro;

---
### Conjunction
---

lemma and_elim: if and: P ∧ Q then
	∀R. (P ⟹ Q ⟹ R) ⟹ prop P ⟹ prop Q ⟹ R
:=
	- for R, if PQR: P ⟹ Q ⟹ R :=
		by PQR and_elim1[OF and] and_elim2[OF and];
	done;

lemma iff_cong_and#cong: for P R,
	if PQ: P ⟺ Q, RS: R ⟺ S, [prop P, prop Q, prop R, prop S]
	then P ∧ R ⟺ Q ∧ S
:=
	apply iff_intro;
	- by and_intro #fold PQ RS #elim and_elim;
	- by and_intro #unfold PQ RS #elim and_elim;
	done;

interpret and: Magma prop (∧) :=
	- done;
	done;

interpret and: Symmetric prop (∧) :=
	- by and_intro #elim and_elim;
	done;

interpret and_iff: Commutative prop (∧) (⟺) :=
	- for P Q, if [prop P, prop Q] then P ∧ Q ⟺ Q ∧ P :=
		apply iff_intro;
		- if [P ∧ Q] :=
			apply and.sym;
			done;
		- if [Q ∧ P] :=
			apply and.sym;
			done;
		done;
	done;

interpret and_iff: Associative prop (∧) (⟺) :=
	- by iff_intro and_intro #elim and_elim;
	done;

lemma iff_imp_and: if PQ: P ⟺ Q, [prop P, prop Q] then
	(P ⟹ Q) ∧ (Q ⟹ P)
:=	by and_intro #unfold PQ;

lemma iff_iff_and: if [prop P, prop Q] then
	(P ⟺ Q) ⟺ (P ⟹ Q) ∧ (Q ⟹ P)
:=	apply iff_intro;
	- if iff: P ⟺ Q :=
		by iff_imp_and[OF iff];
	- if and: (P ⟹ Q) ∧ (Q ⟹ P) :=
		apply iff_intro;
		- by and_elim1[OF and];
		- by and_elim2[OF and];
		done;
	done;

lemma and_imp_iff: if [prop P, prop Q, prop R] then
	(P ∧ Q ⟹ R) ⟺ (P ⟹ Q ⟹ R)
:=	apply iff_intro;
	- if imp: P ∧ Q ⟹ R :=
		by imp and_intro;
	- if imp: P ⟹ Q ⟹ R :=
		by imp #elim and_elim;
	done;

lemma true_and_iff: if [prop P] then true ∧ P ⟺ P :=
	apply iff_intro;
	- if and: true ∧ P :=
		by and_elim2[OF and];
	by and_intro[OF true_intro];

lemma true_and_true: true ∧ true :=
	by #unfold true_and_iff;

lemma and_true_iff: if [prop P] then P ∧ true ⟺ P
:=	unfold and_iff.commute;
	by #unfold true_and_iff;

lemma iff_iff_and: if [prop P, prop Q] then
	(P ⟺ Q) ⟺ (P ⟹ Q) ∧ (Q ⟹ P)
:=	apply iff_intro;
	- if PQ: P ⟺ Q :=
		unfold PQ;
		by and_intro;
	- if and: (P ⟹ Q) ∧ (Q ⟹ P) :=
		apply and_elim[OF and];
		- if PQ: P ⟹ Q, QP: Q ⟹ P :=
			apply iff_intro;
			- by PQ;
			by QP;
		done;
	done;

lemma nand_intro1: if nP: ¬P, [prop P, prop Q] then ¬(P ∧ Q) :=
	apply not_intro;
	- if PQ: P ∧ Q then false :=
		by not_imp_false[OF nP] and_elim1[OF PQ];
	done;

lemma nand_intro2: for P Q, if nQ: ¬Q, [prop P, prop Q] then ¬(P ∧ Q) :=
	apply not_intro;
	- if PQ: P ∧ Q then false :=
		by not_imp_false[OF nQ] and_elim2[OF PQ];
	done;

lemma nand_iff_imp_not: if [prop P, prop Q] then ¬(P ∧ Q) ⟺ (P ⟹ ¬Q) :=
	unfold+ not_iff_imp_false and_imp_iff;
	done;

lemma non_contradiction: if [prop P] then ¬(P ∧ ¬P) :=
	unfold nand_iff_imp_not;
	by nnot_intro;

lemma nand_nnot_iff: if [prop P, prop Q] then ¬(P ∧ ¬¬Q) ⟺ ¬(P ∧ Q) :=
	unfold+ nand_iff_imp_not;
	unfold nnnot_iff;
	done;

lemma nnot_nand_iff: if [prop P, prop Q] then ¬(¬¬P ∧ Q) ⟺ ¬(P ∧ Q) :=
	unfold and_iff.commute;
	unfold nand_nnot_iff;
	unfold and_iff.commute;
	done;

---
### Disjunction
---

lemma or_intro:
	if PQR: ∀R. (P ⟹ R) ⟹ (Q ⟹ R) ⟹ prop R ⟹ R, [prop P, prop Q]
	then P ∨ Q
:=
	apply PQR;
	- by or_intro1;
	- by or_intro2;
	done;

lemma iff_cong_or#cong: for P R,
	if PQ: P ⟺ Q, RS: R ⟺ S, [prop P, prop Q, prop R, prop S]
	then P ∨ R ⟺ Q ∨ S
:=
	apply iff_intro;
	- if PR: P ∨ R :=
		apply or_elim[OF PR];
		- by or_intro1 #fold PQ;
		- by or_intro2 #fold RS;
		done;
	- if QS: Q ∨ S :=
		apply or_elim[OF QS];
		- by or_intro1 #unfold PQ;
		- by or_intro2 #unfold RS;
		done;
	done;

interpret or: Symmetric prop (∨) :=
	- by or_intro #elim or_elim;
	done;

interpret or_iff: Commutative prop (∨) (⟺) :=
	- by iff_intro or_intro #elim or_elim;
	done;

interpret or_iff: Associative prop (∨) (⟺) :=
	- for P Q R, if [prop P, prop Q, prop R] then P ∨ Q ∨ R ⟺ P ∨ (Q ∨ R) :=
		apply iff_intro;
		- if PQR: P ∨ Q ∨ R :=
			apply or_elim[OF PQR];
			- if PQ: P ∨ Q :=
				apply or_elim[OF PQ];
				- by or_intro1;
				- if [Q] :=
					apply or_intro2;
					apply or_intro1;
					done;
				done;
			- if [R] :=
				apply or_intro2;
				apply or_intro2;
				done;
			done;
		- if PQR: P ∨ (Q ∨ R) :=
			apply or_elim[OF PQR];
			- if [P] :=
				apply or_intro1;
				apply or_intro1;
				done;
			- if QR: Q ∨ R :=
				apply or_elim[OF QR];
				- if [Q] :=
					apply or_intro1;
					apply or_intro2;
					done;
				by or_intro2;
			done;
		done;
	done;

lemma or_imp_iff:
	if [prop P, prop Q, prop R]
	then (P ∨ Q ⟹ R) ⟺ (P ⟹ R) ∧ (Q ⟹ R)
:=
	apply iff_intro;
	- if nor: P ∨ Q ⟹ R :=
		by and_intro nor or_intro;
	by #elim or_elim and_elim;

lemma nor_iff: if [prop P, prop Q] then ¬(P ∨ Q) ⟺ ¬P ∧ ¬Q :=
	unfold+ not_iff_imp_false;
	by or_imp_iff;

lemma nnot_nor_iff: if [prop P, prop Q] then ¬(¬¬P ∨ Q) ⟺ ¬(P ∨ Q) :=
	unfold+ nor_iff nnnot_iff;
	by iff.refl;

lemma nor_nnot_iff: if [prop P, prop Q] then ¬(P ∨ ¬¬Q) ⟺ ¬(P ∨ Q) :=
	unfold+ nor_iff nnnot_iff;
	by iff.refl;

lemma nnot_excluded_middle: if [prop P] then ¬¬(P ∨ ¬P) :=
	unfold nor_iff;
	by non_contradiction;

lemma or_imp_nand: if PQ: P ∨ Q, [prop P, prop Q] then ¬(¬P ∧ ¬Q) :=
	apply not_intro;
	apply or_elim[OF PQ];
	- by not_imp_false(P) #elim and_elim;
	- by not_imp_false(Q) #elim and_elim;
	done;

lemma false_or_false_iff: false ∨ false ⟺ false :=
	apply iff_intro;
	by or_intro1 #elim or_elim;

lemma true_or: if [prop P] then true ∨ P :=
	by or_intro1;

lemma or_true: if [prop P] then P ∨ true :=
	by or_intro2;

lemma nnand_iff: if [prop P, prop Q] then ¬¬(P ∧ Q) ⟺ ¬¬P ∧ ¬¬Q :=
	fold nnot_nand_iff;
	fold nand_nnot_iff;
	fold nor_iff;
	by #unfold nnnot_iff;

lemma nniff_iff: if [prop P, prop Q] then ¬¬(¬P ⟺ ¬Q) ⟺ ¬P ⟺ ¬Q :=
	unfold[0]+ iff_iff_and nnand_iff nnimp_not_iff;
	by #fold[0] iff_iff_and;
