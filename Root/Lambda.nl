------
# Untyped Lambda Calculus

We axiomatize untyped lambda calculus, and define logical operations, and arrive at untyped multivalued intuitionistic logic.
------
base Root;

import Equal;

prefix λ 0 0;
fix (λ);
assume beta: (λx. α.[x]) s = α.[s];

import Ext;

setup conclude eq.refl;

setup rewrite eq.refl eq.sym eq.trans eq_prop1;

setup cong eq_cong: f x, eq_ext! x. α.[x];

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

define (and_def) P ∧ Q := ∀R. (P ⟹ Q ⟹ R) ⟹ R;

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

interpret Equal_Iff;
interpret PositiveLogic;

setup conclude iff.refl;

setup rewrite[iff] iff.refl iff.sym iff.trans iff_elim1;
setup cong[iff]
	iff_cong_imp: P ⟹ Q,
	iff_cong_iff: P ⟺ Q,
	iff_cong_and: P ∧ Q,
	iff_cong_all! (∀x. α.[x]);

infix ≠ 50 50 50;

locale DefineNot false :=
	define (not_def) ¬ P := P ⟹ false;
	interpret Not false (¬) :=
		discharge if nP: ¬P, P: P then false;
			by nP[unfolded not_def][OF P];
		discharge if nP: P ⟹ false then ¬P;
			by nP[folded not_def];
		end;

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
	end;

locale DefineFalse :=
	define false := ∀P. P;
	interpret False :=
		substitute false;
			show! if f: false then P;
				by f[unfolded false_def];
			qed;
		end;
	interpret DefineNot;
	end;

locale DefineOr :=
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
	end;

locale DefineEx :=
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
	end;

locale TwoValuedLambda :=
	import TwoValued;
	show eq_true: if P: P then P = true;
		by imp_imp_eq[OF P true_intro];
	show true_eq: if P: P then true = P;
		unfold eq_true[OF P];
		done;
	show eq_refl_eq_true: (x = x) = true;
		by eq_true[OF eq.refl];
	show weaken_eq: (P ⟹ Q ⟹ P) = true;
		by eq_true[OF weaken];
	show eq_true_iff: P = true ⟺ P;
		apply iff_intro;
		case Pt: P = true;
			unfold Pt;
			done;
		by eq_true;
	show true_eq_iff: true = P ⟺ P;
		unfold[iff] eq_iff.commute;
		by eq_true_iff;
	show imp_true_eq: (P ⟹ true) = true;
		by eq_true[OF weaken[OF true_intro]];
	show true_and_true_eq: (true ∧ true) = true;
		by eq_true[OF true_and_true];
	---
	Moreover, we assume that the following identity.
	---
	show true_imp_eq: (true ⟹ P) = P;
		by imp_eq[OF true_intro];
	end;

locale TwoValuedNot :=
	fix false;
	import TwoValuedLambda;
	interpret DefineNot;
	show not_false_eq: (¬false) = true;
		apply eq_true;
		by not_false;
	show not_true_eq: (¬true) = false;
		unfold not_def;
		by true_imp_eq;
	end;
