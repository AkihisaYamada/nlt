---
# Propositional Logic
---

base Root;

fix prop; -- We axiomatize what expressions are propositions.

assume prop_prop#concl: prop (prop x);

---
Implication yields a prop if the condition is a prop,
and the conclusion is prop if the condition is satisfied.
---
assume prop_imp_intro#intro: prop P ⟹ (P ⟹ prop Q) ⟹ prop (P ⟹ Q);

interpret imp: Magma prop (⟹) :=
	- if [prop P, prop Q] then prop (P ⟹ Q) :=
		done;
	end;

---
The universal quantifier yields a prop if the body is a prop for any argument.
---
import all: Binder prop (∀);

note #intro: all.type;

---
The true and false propositions can be obtained.
---
obtain true where true_intro#concl: true, true.type#concl: prop true :=
	- for thesis, if assm: ∀true. true ⟹ prop true ⟹ thesis :=
		by assm(∀P. prop P ⟹ P ⟹ P);
	done;

interpret true: Member prop true :=
	- prop true :=
		done;
	end;

interpret True :=
	substitute true :=
		by true_intro;
	end;

obtain false where false_elim: ∀P. false ⟹ prop P ⟹ P, false.type #concl: prop false :=
	- for thesis, if assm: ∀false. (∀P. false ⟹ prop P ⟹ P) ⟹ prop false ⟹ thesis :=
		apply assm(∀P. prop P ⟹ P);
		- for P, if f: ∀P. prop P ⟹ P, p: prop P :=
			by f[OF p];
		done;
	qed;

interpret false: Member prop false :=
	- prop false :=
		done;
	end;

---
## Logical Connectives

Here axiomatizes logical connectives.
---

----
### Negation
----

fix (¬);
import not: Unary prop (¬);

note #intro: not.type;

assume not_intro: (P ⟹ false) ⟹ prop P ⟹ ¬ P;
assume not_imp_false: ¬ P ⟹ P ⟹ prop P ⟹ false;

show not_false: ¬false :=
	by not_intro;

show nnot_intro: if [P, prop P] then ¬¬P :=
	apply not_intro;
	- if nP: ¬P :=
		by not_imp_false[OF nP];
	done;

show nnot_imp: if imp: ¬¬P ⟹ Q, [P, prop P] then Q :=
	by imp nnot_intro;

show imp_not: if [P], nQ: ¬Q, [prop P, prop Q] then ¬(P ⟹ Q) :=
	apply not_intro;
	- if PQ: P ⟹ Q :=
		by not_imp_false[OF nQ] PQ;
	done;

show imp_not_imp: if PQ: P ⟹ Q, nQ: ¬Q, [prop P, prop Q] then ¬P :=
	apply not_intro;
	by not_imp_false[OF nQ] PQ;

show imp_not_sym: if PnQ: P ⟹ ¬Q, [Q, prop P, prop Q] then ¬P :=
	apply not_intro;
	- if [P] :=
		show nQ: ¬Q :=
			by PnQ;
		by not_imp_false[OF nQ];
	done;

show nnot_imp_nnot: if nnP: ¬¬P, PQ: P ⟹ Q, [prop P, prop Q] then ¬¬Q :=
	apply not_intro;
	- if nQ: ¬Q :=
		show nP: ¬P :=
			by imp_not_imp[OF PQ nQ];
		by not_imp_false[OF nnP] nP;
	done;

show nnimp_imp_nnot: if nnPQ: ¬¬(P ⟹ Q), [P, prop P, prop Q] then ¬¬Q :=
	apply not_intro;
	- if nQ: ¬Q :=
		apply+ not_imp_false[OF nnPQ] not_intro;
		- if PQ: P ⟹ Q :=
			by not_imp_false[OF nQ] PQ;
		by prop_imp_intro;
	done;

show nnot_not_imp_nimp: if nnP: ¬¬P, nQ: ¬Q, [prop P, prop Q] then ¬(P ⟹ Q) :=
	apply not_intro;
	- if PQ: P ⟹ Q :=
		show nnQ: ¬¬Q :=
			by nnot_imp_nnot[OF nnP] PQ;
		by not_imp_false[OF nnQ nQ];
	by prop_imp_intro;

show not_imp_not_all: if nax: ¬α.[x], pa: ∀x. prop α.[x] then ¬(∀y. α.[y]) :=
	apply not_intro;
	- if a: ∀y. α.[y] :=
		by not_imp_false[OF nax] a pa;
	by pa;

----
### Conjunction
----

fix (∧);
import and: Magma prop (∧);
assume and_intro: P ⟹ Q ⟹ prop P ⟹ prop Q ⟹ P ∧ Q;
assume and_elim1: P ∧ Q ⟹ prop P ⟹ prop Q ⟹ P;
assume and_elim2: P ∧ Q ⟹ prop P ⟹ prop Q ⟹ Q;

note #intro: and.type;

interpret and: Symmetric prop (∧) :=
	- if PQ: P ∧ Q, [prop P, prop Q] then Q ∧ P :=
		by and_intro and_elim1[OF PQ] and_elim2[OF PQ];
	end;

fix (⟺);
import iff: Magma prop (⟺);
assume iff_intro: (P ⟹ Q) ⟹ (Q ⟹ P) ⟹ prop P ⟹ prop Q ⟹ (P ⟺ Q);
assume iff_elim1: (P ⟺ Q) ⟹ P ⟹ prop P ⟹ prop Q ⟹ Q;
assume iff_elim2: (P ⟺ Q) ⟹ Q ⟹ prop P ⟹ prop Q ⟹ P;

note #intro: iff.type;

interpret iff: Reflexive prop (⟺) :=
	- if #concl: prop P then P ⟺ P :=
		by iff_intro;
	end;

interpret iff: Symmetric prop (⟺) :=
	- if PQ: P ⟺ Q, [prop P, prop Q] then Q ⟺ P :=
		apply iff_intro;
		blast iff_elim2[OF PQ];
		by iff_elim1[OF PQ];
	end;

interpret iff: Transitive prop (⟺) :=
	- if PQ: P ⟺ Q, QR: Q ⟺ R, [prop P, prop Q, prop R] then P ⟺ R :=
		apply iff_intro;
		blast iff_elim1[OF QR] iff_elim1[OF PQ];
		by iff_elim2[OF PQ] iff_elim2[OF QR];
	end;

show imp_imp_iff: if [P, prop P, prop Q] then (P ⟹ Q) ⟺ Q :=
	apply iff_intro;
	- if PQ: P ⟹ Q :=
		by PQ;
	- if [Q, P] :=
		done;
	done;

show iff_cong_imp:
	if PQ: P ⟺ Q, RS: R ⟺ S, [prop P, prop Q, prop R, prop S]
	then (P ⟹ R) ⟺ (Q ⟹ S) :=
	apply iff_intro;
	- if PR: P ⟹ R, [Q] :=
		by iff_elim1[OF RS] PR iff_elim2[OF PQ];
	- if QS: Q ⟹ S, [P] :=
		by iff_elim2[OF RS] QS iff_elim1[OF PQ];
	done;

show iff_cong_iff:
	if PQ: P ⟺ Q, RS: R ⟺ S, [prop P, prop Q, prop R, prop S]
	then (P ⟺ R) ⟺ (Q ⟺ S) :=
	apply iff_intro;
	- if PR: P ⟺ R :=
		show QP: Q ⟺ P :=
			by iff.sym[OF PQ];
		show QR: Q ⟺ R :=
			by iff.trans[OF QP PR];
		by iff.trans[OF QR RS];
	- if QS: Q ⟺ S :=
		show PS: P ⟺ S :=
			by iff.trans[OF PQ QS];
		show SR: S ⟺ R :=
			by iff.sym[OF RS];
		by iff.trans[OF PS SR];
	done;

show iff_cong_all:
	if ab: ∀x. α.[x] ⟺ β.[x], [∀x. prop α.[x], ∀x. prop β.[x]]
	then (∀x. α.[x]) ⟺ (∀x. β.[x]) :=
	apply iff_intro;
	- if a: ∀x. α.[x] :=
		by iff_elim1[OF ab] a;
	- if b: ∀x. β.[x] :=
		by iff_elim2[OF ab] b;
	done;

show imp_iff_iff: if [P, prop P, prop Q] then (P ⟺ Q) ⟺ Q :=
	apply iff_intro;
	- if PQ: P ⟺ Q :=
		by iff_elim1[OF PQ];
	- if [Q] :=
		by iff_intro;
	done;

show all_imp2_iff: if [prop P] then (∀Q. prop Q ⟹ (P ⟹ Q) ⟹ Q) ⟺ P :=
	apply iff_intro;
	- if all: ∀Q. prop Q ⟹ (P ⟹ Q) ⟹ Q :=
		apply all;
		done;
	- if [P] :=
		- for Q, if [prop Q], PQ: P ⟹ Q :=
			by PQ;
		qed;
	done;

show imp3_iff: if [prop P, prop Q] then (((P ⟹ Q) ⟹ Q) ⟹ Q) ⟺ (P ⟹ Q) :=
	apply iff_intro;
	- := just imp2_imp_imp;
	- if PQ: P ⟹ Q, PQQ: (P ⟹ Q) ⟹ Q then Q :=
		by PQQ[OF PQ];
	done;

show imp_all_iff: if [prop P, ∀x. prop α.[x]] then (P ⟹ ∀x. α.[x]) ⟺ (∀x. P ⟹ α.[x]) :=
	by iff_intro[OF imp_all all_imp];

show imp_iff_iff1: if [P, prop P, prop Q] then (P ⟺ Q) ⟺ Q :=
	apply iff_intro;
	- if PQ: P ⟺ Q :=
		by iff_elim1[OF PQ];
	- if [Q] :=
		by iff_intro;
	done;

show iff_imp_and: if PQ: P ⟺ Q, [prop P, prop Q] then (P ⟹ Q) ∧ (Q ⟹ P) :=
	apply and_intro;
	- := by iff_elim1[OF PQ];
	- := by iff_elim2[OF PQ];
	done;

show iff_iff_and: if [prop P, prop Q] then (P ⟺ Q) ⟺ (P ⟹ Q) ∧ (Q ⟹ P) :=
	apply iff_intro;
	- if iff: P ⟺ Q :=
		by iff_imp_and[OF iff];
	- if and: (P ⟹ Q) ∧ (Q ⟹ P) :=
		apply iff_intro;
		- := by and_elim1[OF and];
		- := by and_elim2[OF and];
		done;
	done;

show and_iff: if [prop P, prop Q] then
	(P ∧ Q) ⟺ (∀R. prop R ⟹ (P ⟹ Q ⟹ R) ⟹ R)
:=
	apply iff_intro;
	- if and: P ∧ Q :=
		- for R, if [prop R], PQR: P ⟹ Q ⟹ R :=
			by PQR and_elim1[OF and] and_elim2[OF and];
		qed;
	- if all: ∀R. prop R ⟹ (P ⟹ Q ⟹ R) ⟹ R :=
		apply all;
		by and_intro;
	done;

fix (∨);
import or: Magma prop (∨);
assume or_intro1: P ⟹ prop P ⟹ prop Q ⟹ P ∨ Q;
assume or_intro2: ∀P. ∀Q. Q ⟹ prop P ⟹ prop Q ⟹ P ∨ Q;
assume or_elim: P ∨ Q ⟹ (P ⟹ R) ⟹ (Q ⟹ R) ⟹ prop P ⟹ prop Q ⟹ prop R ⟹ R;

note #intro: or.type;

interpret Symmetric prop (∨) :=
	- if or: P ∨ Q, [prop P, prop Q] then Q ∨ P :=
		apply or_elim[OF or];
		- := by or_intro2;
		- := by or_intro1;
		done;
	end;

show or_iff: if [prop P, prop Q] then
	(P ∨ Q) ⟺ (∀R. prop R ⟹ (P ⟹ R) ⟹ (Q ⟹ R) ⟹ R)
:=
	apply iff_intro;
	- if or: P ∨ Q :=
		- for R, if [prop R], PR: P ⟹ R, QR: Q ⟹ R :=
			apply or_elim[OF or];
			- := by PR;
			- := by QR;
			done;
		qed;
	- if all: ∀R. prop R ⟹ (P ⟹ R) ⟹ (Q ⟹ R) ⟹ R :=
		apply all;
		- := done;
		- := by or_intro1;
		- := by or_intro2;
		qed;
	done;


---
### Existence
---

fix (∃);
import ex: Binder prop (∃);
assume ex_intro1: ∀x. ∀α. α.[x] ⟹ (∀y. prop α.[y]) ⟹ ∃z. α.[z];
assume ex_elim: (∃x. α.[x]) ⟹ (∀x. α.[x] ⟹ P) ⟹ (∀y. prop α.[y]) ⟹ prop P ⟹ P;

note #intro: ex.type;

show ex_intro:
	if assm: ∀P. prop P ⟹ (∀x. α.[x] ⟹ P) ⟹ P, [∀x. prop α.[x]]
	then ∃x. α.[x]
:=
	apply assm;
	- := done;
	- for x, if ax: α.[x] :=
		 by ex_intro1[OF ax];
	done;

show ex_imp_all_imp:
	if ex: ∃x. α.[x] ⟹ P, [∀x. α.[x], ∀x. prop α.[x], prop P] then P
:=
	apply ex_elim[OF ex];
	- for x, if imp: α.[x] ⟹ P :=
		by imp;
	done;

show ex_iff:
	if [∀x. prop α.[x]] then (∃x. α.[x]) ⟺ (∀P. prop P ⟹ (∀x. α.[x] ⟹ P) ⟹ P)
:=
	apply iff_intro;
	- if ex: ∃x. α.[x] :=
		- for P, if [prop P], all: ∀x. α.[x] ⟹ P :=
			by ex_elim[OF ex all];
		qed;
	- if all: ∀P. prop P ⟹ (∀x. α.[x] ⟹ P) ⟹ P :=
		by ex_intro[OF all];
	done;

locale ExcludedMiddle :=
	assume excluded_middle: prop P ⟹ P ∨ ¬P;
	end;
