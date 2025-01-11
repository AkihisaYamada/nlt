---
# Propositional Logic
---

base Root;

fix prop; -- We axiomatize what expressions are propositions.

assume prop_prop: prop (prop x);

---
Implication yields a prop if the condition is a prop,
and the conclusion is prop if the condition is satisfied.
---
assume prop_imp_intro: prop P ⟹ (P ⟹ prop Q) ⟹ prop (P ⟹ Q);

interpret imp: Magma prop (⟹) :=
	discharge if pP: prop P, pQ: prop Q then prop (P ⟹ Q) :=
		by prop_imp_intro pP pQ;
	end;

---
The universal quantifier yields a prop if the body is a prop for any argument.
---
import all: Binder prop (∀);

---
The true and false propositions can be obtained.
---
obtain true where true_intro: true, true.type: prop true :=
	case for thesis, assm: ∀true. true ⟹ prop true ⟹ thesis :=
		apply assm(∀P. prop P ⟹ P ⟹ P);
		by all.type prop_imp_intro prop_prop;
	qed;

interpret true: Member prop true :=
	discharge prop true :=
		by true.type;
	end;

interpret True :=
	substitute true :=
		by true_intro;
	end;

obtain false where false_elim: ∀P. false ⟹ prop P ⟹ P, false.type: prop false :=
	case for thesis, assm: ∀false. (∀P. false ⟹ prop P ⟹ P) ⟹ prop false ⟹ thesis :=
		apply assm(∀P. prop P ⟹ P);
		case for P, f: ∀P. prop P ⟹ P, p: prop P :=
			by f[OF p];
		by all.type prop_imp_intro prop_prop;
	qed;

interpret false: Member prop false :=
	discharge prop false :=
		by false.type;
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
assume not_intro: (P ⟹ false) ⟹ prop P ⟹ ¬ P;
assume not_imp_false: ¬ P ⟹ P ⟹ prop P ⟹ false;

show not_false: ¬false :=
	by not_intro false.type;

show nnot_intro: if P: P, pP: prop P then ¬¬P :=
	apply not_intro;
	case nP: ¬P :=
		by not_imp_false[OF nP P pP];
	qed;

show nnot_imp: if imp: ¬¬P ⟹ Q, P: P, pP: prop P then Q :=
	by imp nnot_intro P not.type pP;

show imp_not: if P: P, nQ: ¬Q, pP: prop P, pQ: prop Q then ¬(P ⟹ Q) :=
	apply not_intro;
	case PQ: P ⟹ Q :=
		note Q: PQ[OF P];
		by not_imp_false[OF nQ Q pQ];
	by prop_imp_intro pP pQ;

show imp_not_imp: if PQ: P ⟹ Q, nQ: ¬Q, pP: prop P, pQ: prop Q then ¬P :=
	apply not_intro;
	show! if P: P then false :=
		by not_imp_false[OF nQ] PQ P pQ;
	by pP;

show imp_not_sym: if PnQ: P ⟹ ¬Q, Q: Q, pP: prop P, pQ: prop Q then ¬P :=
	apply not_intro;
	case P: P :=
		show nQ: ¬Q :=
			by PnQ[OF P];
		by not_imp_false[OF nQ] Q pQ;
	by pP;

show nnot_imp_nnot: if nnP: ¬¬P, PQ: P ⟹ Q, pP: prop P, pQ: prop Q then ¬¬Q :=
	apply not_intro;
	case nQ: ¬Q :=
		show nP: ¬P :=
			by imp_not_imp[OF PQ nQ] pP pQ;
		by not_imp_false[OF nnP] nP not.type pP;
	by not.type pQ;

show nnimp_imp_nnot: if nnPQ: ¬¬(P ⟹ Q), P: P, pP: prop P, pQ: prop Q then ¬¬Q :=
	apply not_intro;
	case nQ: ¬Q :=
		apply+ not_imp_false[OF nnPQ] not_intro;
		case PQ: P ⟹ Q :=
			by not_imp_false[OF nQ] PQ P pQ;
		by prop_imp_intro pP pQ not.type;
	by not.type pQ;

show nnot_not_imp_nimp: if nnP: ¬¬P, nQ: ¬Q, pP: prop P, pQ: prop Q then ¬(P ⟹ Q) :=
	apply not_intro;
	case PQ: P ⟹ Q :=
		show nnQ: ¬¬Q :=
			by nnot_imp_nnot[OF nnP] PQ;
		by not_imp_false[OF nnQ] nQ not.type;
	by prop_imp_intro;

show not_imp_not_all: if nax: ¬α.[x], pa: ∀x. prop α.[x] then ¬(∀y. α.[y]) :=
	apply not_intro;
	case a: ∀y. α.[y] :=
		by not_imp_false[OF nax] a pa;
	by all.type pa;

----
### Conjunction
----

fix (∧);
import and: Magma prop (∧);
assume and_intro: P ⟹ Q ⟹ prop P ⟹ prop Q ⟹ P ∧ Q;
assume and_elim1: P ∧ Q ⟹ prop P ⟹ prop Q ⟹ P;
assume and_elim2: P ∧ Q ⟹ prop P ⟹ prop Q ⟹ Q;

interpret and: Symmetric prop (∧) :=
	discharge if PQ: P ∧ Q, pP: prop P, qQ: prop Q then Q ∧ P :=
		by and_intro and_elim1[OF PQ] and_elim2[OF PQ] pP qQ;
	end;

fix (⟺);
import iff: Magma prop (⟺);
assume iff_intro: (P ⟹ Q) ⟹ (Q ⟹ P) ⟹ prop P ⟹ prop Q ⟹ (P ⟺ Q);
assume iff_elim1: (P ⟺ Q) ⟹ P ⟹ prop P ⟹ prop Q ⟹ Q;
assume iff_elim2: (P ⟺ Q) ⟹ Q ⟹ prop P ⟹ prop Q ⟹ P;

interpret iff: Reflexive prop (⟺) :=
	discharge if pP: prop P then P ⟺ P :=
		by iff_intro;
	end;

interpret iff: Symmetric prop (⟺) :=
	discharge if PQ: P ⟺ Q, pP: prop P, pQ: prop Q then Q ⟺ P :=
		apply iff_intro;
		blast iff_elim2[OF PQ];
		by iff_elim1[OF PQ];
	end;

interpret iff: Transitive prop (⟺) :=
	discharge if PQ: P ⟺ Q, QR: Q ⟺ R, pP: prop P, pQ: prop Q, pR: prop R then P ⟺ R :=
		apply iff_intro;
		blast iff_elim1[OF QR] iff_elim1[OF PQ];
		by iff_elim2[OF PQ] iff_elim2[OF QR];
	end;

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
