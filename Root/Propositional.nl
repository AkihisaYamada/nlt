---
# Propositional Logic
---

base Root;

fix prop; -- We axiomatize what expressions are propositions.

assume prop_prop#intro: prop (prop x);

---
Implication yields a prop if the condition is a prop,
and the conclusion is prop if the condition is satisfied.
---
assume prop_imp_intro#intro: prop P ⟹ (P ⟹ prop Q) ⟹ prop (P ⟹ Q);

interpret imp: Magma prop (⟹) :=
	- if #concl: prop P, #concl: prop Q then prop (P ⟹ Q) :=
		by;
	end;

---
The universal quantifier yields a prop if the body is a prop for any argument.
---
import all: Binder prop (∀);

note #intro: all.type;

---
The true and false propositions can be obtained.
---
obtain true where true_intro #concl: true, true.type #concl: prop true :=
	- for thesis, if assm: ∀true. true ⟹ prop true ⟹ thesis :=
		apply assm(∀P. prop P ⟹ P ⟹ P);
		- for P, if pP: prop P, P: P :=
			by P;
		done;
	done;

interpret true: Member prop true :=
	- prop true :=
		by true.type;
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
		by all.type prop_imp_intro prop_prop;
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

show nnot_intro: if P: P, #concl: prop P then ¬¬P :=
	apply not_intro;
	- if nP: ¬P :=
		by not_imp_false[OF nP P];
	done;

show nnot_imp: if imp: ¬¬P ⟹ Q, P: P, #concl: prop P then Q :=
	by imp nnot_intro P;

show imp_not: if P: P, nQ: ¬Q, #concl: prop P, #concl: prop Q then ¬(P ⟹ Q) :=
	apply not_intro;
	- if PQ: P ⟹ Q :=
		note Q: PQ[OF P];
		by not_imp_false[OF nQ Q];
	done;

show imp_not_imp: if PQ: P ⟹ Q, nQ: ¬Q, #concl: prop P, #concl: prop Q then ¬P :=
	apply not_intro;
	- if P: P then false :=
		by not_imp_false[OF nQ] PQ P;
	done;

show imp_not_sym: if PnQ: P ⟹ ¬Q, Q: Q, #concl: prop P, #concl: prop Q then ¬P :=
	apply not_intro;
	- if P: P :=
		show nQ: ¬Q :=
			by PnQ[OF P];
		by not_imp_false[OF nQ] Q;
	done;

show nnot_imp_nnot: if nnP: ¬¬P, PQ: P ⟹ Q, #concl: prop P, #concl: prop Q then ¬¬Q :=
	apply not_intro;
	- if nQ: ¬Q :=
		show nP: ¬P :=
			by imp_not_imp[OF PQ nQ];
		by not_imp_false[OF nnP] nP;
	done;

show nnimp_imp_nnot: if nnPQ: ¬¬(P ⟹ Q), P: P, #concl: prop P, #concl: prop Q then ¬¬Q :=
	apply not_intro;
	- if nQ: ¬Q :=
		apply+ not_imp_false[OF nnPQ] not_intro;
		- if PQ: P ⟹ Q :=
			by not_imp_false[OF nQ] PQ P;
		by prop_imp_intro;
	done;

show nnot_not_imp_nimp: if nnP: ¬¬P, nQ: ¬Q, #concl: prop P, #concl: prop Q then ¬(P ⟹ Q) :=
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

interpret and: Symmetric prop (∧) :=
	- if PQ: P ∧ Q, #concl: prop P, #concl: prop Q then Q ∧ P :=
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
	- if PQ: P ⟺ Q, #concl: prop P, #concl: prop Q then Q ⟺ P :=
		apply iff_intro;
		blast iff_elim2[OF PQ];
		by iff_elim1[OF PQ];
	end;

interpret iff: Transitive prop (⟺) :=
	- if PQ: P ⟺ Q, QR: Q ⟺ R, #concl: prop P, #concl: prop Q, #concl: prop R then P ⟺ R :=
		apply iff_intro;
		blast iff_elim1[OF QR] iff_elim1[OF PQ];
		by iff_elim2[OF PQ] iff_elim2[OF QR];
	end;

show imp_imp_iff: if P: P, pP: prop P, pQ: prop Q then (P ⟹ Q) ⟺ Q :=
	apply iff_intro;
	- if PQ: P ⟹ Q :=
		by PQ[OF P];
	- if Q: Q, P2: P :=
		by Q;
	done;

show iff_cong_imp:
	if PQ: P ⟺ Q, RS: R ⟺ S, pP: prop P, pQ: prop Q, pR: prop R, pS: prop S
	then (P ⟹ R) ⟺ (Q ⟹ S) :=
	apply iff_intro;
	case PR: P ⟹ R, Q: Q :=
		by iff_elim1[OF RS] PR iff_elim2[OF PQ] Q;
	case QS: Q ⟹ S, P: P :=
		by iff_elim2[OF RS] QS iff_elim1[OF PQ] P;
	by;

show iff_cong_iff:
	if PQ: P ⟺ Q, RS: R ⟺ S, pP: prop P, pQ: prop Q, pR: prop R, pS: prop S
	then (P ⟺ R) ⟺ (Q ⟺ S) :=
	apply iff_intro;
	case PR: P ⟺ R :=
		show QP: Q ⟺ P :=
			by iff.sym[OF PQ];
		show QR: Q ⟺ R :=
			by iff.trans[OF QP PR];
		by iff.trans[OF QR RS];
	case QS: Q ⟺ S :=
		show PS: P ⟺ S :=
			by iff.trans[OF PQ QS];
		show SR: S ⟺ R :=
			by iff.sym[OF RS];
		by iff.trans[OF PS SR];
	by;

show iff_cong_all:
	if ab: ∀x. α.[x] ⟺ β.[x], aP: ∀x. prop α.[x], bP: ∀x. prop β.[x]
	then (∀x. α.[x]) ⟺ (∀x. β.[x]) :=
	apply iff_intro;
	case a: ∀x. α.[x] :=
		by iff_elim1[OF ab] a;
	case b: ∀x. β.[x] :=
		by iff_elim2[OF ab] b;
	by aP bP;

show imp_iff_iff: if P: P then (P ⟺ Q) ⟺ Q :=
	apply iff_intro;
	case PQ: P ⟺ Q :=
		apply+ iff_elim1[OF PQ] P;
		qed;
	case Q: Q :=
		by iff_intro P Q;
	qed;

show all_imp2_iff: (∀Q. (P ⟹ Q) ⟹ Q) ⟺ P :=
	apply iff_intro;
	case all: ∀Q. (P ⟹ Q) ⟹ Q :=
		by all[OF imp.refl];
	case P: P :=
		case for Q, PQ: P ⟹ Q :=
			by PQ[OF P];
		qed;
	qed;

show imp3_iff: (((P ⟹ Q) ⟹ Q) ⟹ Q) ⟺ (P ⟹ Q) :=
	apply iff_intro;
	note! imp2_imp_imp;
	show! if PQ: P ⟹ Q, PQQ: (P ⟹ Q) ⟹ Q then Q :=
		by PQQ[OF PQ];
	qed;

show imp_all_iff: (P ⟹ ∀x. α.[x]) ⟺ (∀x. P ⟹ α.[x]) :=
	by iff_intro[OF imp_all all_imp];

show imp_iff_iff1: if P: P then (P ⟺ Q) ⟺ Q :=
	apply iff_intro;
	case PQ: P ⟺ Q :=
		by iff_elim1[OF PQ P];
	case Q: Q :=
		by iff_intro P Q;
	qed;


show iff_imp_and: if PQ: P ⟺ Q, pP: prop P, pQ: prop Q then (P ⟹ Q) ∧ (Q ⟹ P) :=
	apply and_intro;
	blast iff_elim1[OF PQ] pP pQ prop_imp_intro;
	by iff_elim2[OF PQ] pP pQ prop_imp_intro;

show iff_iff_and: if pP: prop P, pQ: prop Q then (P ⟺ Q) ⟺ (P ⟹ Q) ∧ (Q ⟹ P) :=
	apply iff_intro;
	case iff: P ⟺ Q :=
		by iff_imp_and[OF iff pP pQ];
	case and: (P ⟹ Q) ∧ (Q ⟹ P) :=
		apply iff_intro;
		blast and_elim1[OF and] prop_imp_intro;
		blast and_elim2[OF and] prop_imp_intro;
		by pP pQ;
	by iff.type and.type prop_imp_intro pP pQ;

show and_iff: if pP: prop P, pQ: prop Q then
	(P ∧ Q) ⟺ (∀R. prop R ⟹ (P ⟹ Q ⟹ R) ⟹ R)
:=
	apply iff_intro;
	case and: P ∧ Q :=
		case for R, pR: prop R, PQR: P ⟹ Q ⟹ R :=
			by PQR and_elim1[OF and] and_elim2[OF and] pP pQ pR;
		qed;
	case all: ∀R. prop R ⟹ (P ⟹ Q ⟹ R) ⟹ R :=
		apply all;
		by and.type and_intro;
	by and.type all.type prop_imp_intro prop_prop;

fix (∨);
import or: Magma prop (∨);
assume or_intro1: P ⟹ prop P ⟹ prop Q ⟹ P ∨ Q;
assume or_intro2: ∀P. ∀Q. Q ⟹ prop P ⟹ prop Q ⟹ P ∨ Q;
assume or_elim: P ∨ Q ⟹ (P ⟹ R) ⟹ (Q ⟹ R) ⟹ prop P ⟹ prop Q ⟹ prop R ⟹ R;

interpret Symmetric prop (∨) :=
	discharge if or: P ∨ Q, pP: prop P, pQ: prop Q then Q ∨ P :=
		apply or_elim[OF or];
		case P: P :=
			by or_intro2 P pQ;
		case Q: Q :=
			by or_intro1 Q pP;
		by pQ pP or.type;
	end;

show or_iff: if pP: prop P, pQ: prop Q then
	(P ∨ Q) ⟺ (∀R. prop R ⟹ (P ⟹ R) ⟹ (Q ⟹ R) ⟹ R)
:=
	apply iff_intro;
	case or: P ∨ Q :=
		case for R, pR: prop R, PR: P ⟹ R, QR: Q ⟹ R :=
			apply or_elim[OF or];
			case P: P :=
				by PR P;
			case Q: Q :=
				by QR Q;
			by pP pQ pR;
		qed;
	case all: ∀R. prop R ⟹ (P ⟹ R) ⟹ (Q ⟹ R) ⟹ R :=
		apply all;
		blast or.type pP pQ;
		blast or_intro1;
		blast or_intro2;
		qed;
	by or.type all.type prop_imp_intro prop_prop;


---
### Existence
---

fix (∃);
import ex: Binder prop (∃);
assume ex_intro1: ∀x. ∀α. α.[x] ⟹ (∀y. prop α.[y]) ⟹ ∃z. α.[z];
assume ex_elim: (∃x. α.[x]) ⟹ (∀x. α.[x] ⟹ P) ⟹ (∀y. prop α.[y]) ⟹ prop P ⟹ P;

show ex_intro:
	if assm: ∀P. prop P ⟹ (∀x. α.[x] ⟹ P) ⟹ P, atype: ∀x. prop α.[x]
	then ∃x. α.[x]
:=
	apply assm;
	blast ex.type atype;
	case for x, ax: α.[x] :=
		 by ex_intro1[OF ax] atype;
	qed;

show ex_imp_all_imp:
	if ex: ∃x. α.[x] ⟹ P, all: ∀x. α.[x], atype: ∀x. prop α.[x], pP: prop P then P
:=
	apply ex_elim[OF ex];
	case for x, imp: α.[x] ⟹ P :=
		by imp[OF all];
	by pP prop_imp_intro atype;

show ex_iff:
	if pa: ∀x. prop α.[x] then (∃x. α.[x]) ⟺ (∀P. prop P ⟹ (∀x. α.[x] ⟹ P) ⟹ P)
:=
	apply iff_intro;
	case ex: ∃x. α.[x] :=
		case for P, pP: prop P, all: ∀x. α.[x] ⟹ P :=
			by ex_elim[OF ex all pa] pP;
		qed;
	case all: ∀P. prop P ⟹ (∀x. α.[x] ⟹ P) ⟹ P :=
		apply ex_intro[OF all];
		by all.type prop_imp_intro prop_prop pa;
	qed;

locale ExcludedMiddle :=
	assume excluded_middle: prop P ⟹ P ∨ ¬P;
	end;
