------
# Untyped Lambda Calculus

We axiomatize untyped lambda calculus, and define logical operations, and arrive at untyped multivalued intuitionistic logic.
------
base Root;

import Lambda;
import Ext;

setup conclude eq.refl;

setup rewrite eq.refl eq.sym eq.trans eq_prop1;

setup cong
	eq_cong: f x,
	eq_ext! x. α.[x];

setup define = λ beta;

----
## Defining Logical Constructs
----

define true := ∀P. P ⟹ P;

interpret True :=
	substitute true;
		unfold true_def;
		by imp.refl;
	end;

setup conclude true_intro;

show true_eq_imp: if tP: true = P then P;
	fold tP;
	done;

show eq_true_imp: if Pt: P = true then P;
	unfold Pt;
	done;

define false := ∀P. P;

interpret False :=
	substitute false;
		show! if f: false then P;
			by f[unfolded false_def];
		qed;
	end;

define (and_def) P ∧ Q := ∀ R. (P ⟹ Q ⟹ R) ⟹ R;

interpret And (∧) :=
	discharge if P: P, Q: Q then P ∧ Q;
		show 1: if PQR: P ⟹ Q ⟹ R then R;
			by PQR[OF P Q];
		by eq_prop2[OF and_def 1];
	discharge if PQ: P ∧ Q then P;
		show PQP: if P: P, Q: Q then P;
			by P;
		by eq_prop1[OF and_def][OF PQ PQP];
	discharge if PQ: P ∧ Q then Q;
		show PQQ: if P: P, Q: Q then Q;
			by Q;
		by eq_prop1[OF and_def][OF PQ PQQ];
	end;

define (iff_def) P ⟺ Q := (P ⟹ Q) ∧ (Q ⟹ P);

interpret Iff (⟺) :=
	discharge if PQ: P ⟹ Q, QP: Q ⟹ P then P ⟺ Q;
		show and: (P ⟹ Q) ∧ (Q ⟹ P);
			by and_intro[OF PQ QP];
		by and[folded iff_def];
	discharge if PQ: P ⟺ Q then P ⟹ Q;
		by and_elim1[OF PQ[unfolded iff_def]];
	discharge if PQ: P ⟺ Q then Q ⟹ P;
		by and_elim2[OF PQ[unfolded iff_def]];
	end;

show eq_imp_iff: if PQ: P = Q then P ⟺ Q;
	unfold PQ;
	by iff.refl;

show eq_commute: x = y ⟺ y = x;
	by iff_intro[OF eq.sym eq.sym];

define (not_def) ¬ P := P ⟹ false;

interpret Not false (¬) :=
	discharge if nP: ¬P, P: P then false;
		by nP[unfolded not_def][OF P];
	discharge if nP: P ⟹ false then ¬P;
		by nP[folded not_def];
	end;

define (or_def) P ∨ Q := ∀ R. (P ⟹ R) ⟹ (Q ⟹ R) ⟹ R;

interpret Or (∨) :=
	discharge if P: P then P ∨ Q;
		show 1: if PR: P ⟹ R, QR: Q ⟹ R then R;
			by PR[OF P];
		by eq_prop2[OF or_def 1];
	discharge if Q: Q then P ∨ Q;
		show 1: if PR: P ⟹ R, QR: Q ⟹ R then R;
			by QR[OF Q];
		by eq_prop2[OF or_def 1];
	discharge if PQ: P ∨ Q, PR: P ⟹ R, QR: Q ⟹ R then R;
		by eq_prop1[OF or_def PQ PR QR];
	end;

define (ex_def) ∃ α := (∀P. (∀x. α.[x] ⟹ P) ⟹ P);

interpret Ex (∃) :=
	discharge for α x, if ax: α.[x] then ∃x. α.[x];
		unfold ex_def;
		case for P, all: ∀x. α.[x] ⟹ P;
			by all[OF ax];
		qed;
	discharge if ex: ∃x. α.[x] then (∀x. α.[x] ⟹ P) ⟹ P;
		by ex[unfolded ex_def];
	end;

---
This is enough to interpret untyped intuitionistic logic.
---
interpret UntypedLogic;

setup conclude iff.refl;

setup rewrite[iff] iff.refl iff.sym iff.trans iff_elim1;
setup cong[iff]
	iff_cong_imp: P ⟹ Q,
	iff_cong_iff: P ⟺ Q,
	iff_cong_and: P ∧ Q,
	iff_cong_or: P ∨ Q,
	iff_cong_not: ¬P,
	iff_cong_all! (∀x. α.[x]),
	iff_cong_ex! (∃x. α.[x]);

----
## Unequal
----
infix ≠ 50 50 50;

define (neq_def) x ≠ y := ¬ x = y;

show neq_intro: if xyf: x = y ⟹ false then x ≠ y;
	unfold neq_def;
	apply not_intro;
	by xyf;

note neq_elim: eq_prop1[OF neq_def];

show neq_irrefl: ¬ x ≠ x;
	unfold neq_def;
	apply nnot_intro;
	by eq.refl;

show true_Neq_false: true ≠ false;
	apply neq_intro;
	show! if tf: true = false then false;
		fold tf;
		by true_intro;
	qed;
