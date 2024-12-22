------
# Untyped Lambda Calculus

We axiomatize untyped lambda calculus, and define logical operations, and arrive at untyped multivalued intuitionistic logic.
------
base Root;

import Equal;

prefix λ 0 0;
fix (λ);
assume beta: (λx. α.[x]) s = α.[s];

setup conclude eq.refl;

setup rewrite eq_prop1 eq.refl eq.trans;
setup dual eq.sym;

setup cong eq_cong eq_cong_abs;

setup define beta;

----
## Defining Logical Constructs
----

define true := ∀P. P ⟹ P;

interpret True :=
	substitute true :=
		unfold true_def;
		by imp.refl;
	end;

setup conclude true_intro;

show true_eq_imp: if tP: true = P then P :=
	fold tP;
	done;

show eq_true_imp: if Pt: P = true then P :=
	unfold Pt;
	done;

define (and_def) P ∧ Q := ∀R. (P ⟹ Q ⟹ R) ⟹ R;

interpret And (∧) :=
	discharge if P: P, Q: Q then P ∧ Q :=
		apply eq_prop2[OF and_def];
		case for R, PQR: P ⟹ Q ⟹ R :=
			by PQR[OF P Q];
		qed;
	discharge if PQ: P ∧ Q then P :=
		apply eq_prop1[OF and_def][OF PQ];
		case P: P, Q: Q :=
			by P;
		qed;
	discharge if PQ: P ∧ Q then Q :=
		apply eq_prop1[OF and_def][OF PQ];
		case P: P, Q: Q :=
			by Q;
		qed;
	end;

define (iff_def) P ⟺ Q := (P ⟹ Q) ∧ (Q ⟹ P);

interpret Iff (⟺) :=
	discharge if PQ: P ⟹ Q, QP: Q ⟹ P then P ⟺ Q :=
		apply eq_prop2[OF iff_def];
		by and_intro[OF PQ QP];
	discharge if PQ: P ⟺ Q then P ⟹ Q :=
		show and: (P ⟹ Q) ∧ (Q ⟹ P) :=
			by eq_prop1[OF iff_def PQ];
		by and_elim1[OF and];
	discharge if PQ: P ⟺ Q then Q ⟹ P :=
		show and: (P ⟹ Q) ∧ (Q ⟹ P) :=
			by eq_prop1[OF iff_def PQ];
		by and_elim2[OF and];
	end;

interpret Equal_Iff;
interpret PositiveLogic;

setup conclude iff.refl;

setup rewrite iff_elim1 iff.refl iff.trans;

setup cong iff_cong_imp iff_cong_iff iff_cong_and iff_cong_all;

setup dual iff.sym;

infix ≠ 50 50 50;

locale DefineNot false :=
	define (not_def) ¬ P := P ⟹ false;
	interpret MinimalNot false (¬) :=
		discharge if nP: ¬P, P: P then false :=
			by nP[unfolded not_def][OF P];
		discharge if nP: P ⟹ false then ¬P :=
			by nP[folded not_def];
		end;

	define (neq_def) x ≠ y := ¬ x = y;

	show neq_intro: if xyf: x = y ⟹ false then x ≠ y :=
		unfold neq_def;
		apply not_intro;
		by xyf;

	note neq_elim: eq_prop1[OF neq_def];

	show neq_irrefl: ¬ x ≠ x :=
		unfold neq_def;
		apply nnot_intro;
		by eq.refl;

	show neq_imp_false: if neq: x ≠ y, eq: x = y then false :=
		by not_imp_false[OF neq[unfolded neq_def] eq];

	show neq_refl_imp_false: if xx: x ≠ x then false :=
		by neq_imp_false[OF xx eq.refl];

	show true_neq_false: true ≠ false :=
		apply neq_intro;
		show! if tf: true = false then false :=
			fold tf;
			by true_intro;
		qed;
	end;

locale DefineFalse :=
	define (false_def) false := ∀P. P;
	interpret False :=
		substitute false :=
			show! if f: false then P :=
				by f[unfolded false_def];
			qed;
		end;
	interpret DefineNot;
	interpret Not;
	end;

locale DefineOr :=
	define (or_def) P ∨ Q := ∀ R. (P ⟹ R) ⟹ (Q ⟹ R) ⟹ R;
	interpret Or (∨) :=
		discharge if P: P then P ∨ Q :=
			show 1: if PR: P ⟹ R, QR: Q ⟹ R then R :=
				by PR[OF P];
			by eq_prop2[OF or_def 1];
		discharge if Q: Q then P ∨ Q :=
			show 1: if PR: P ⟹ R, QR: Q ⟹ R then R :=
				by QR[OF Q];
			by eq_prop2[OF or_def 1];
		discharge if PQ: P ∨ Q, PR: P ⟹ R, QR: Q ⟹ R then R :=
			by eq_prop1[OF or_def PQ PR QR];
		end;
	end;

locale DefineEx :=
	define (ex_def) ∃ α := (∀P. (∀x. α.[x] ⟹ P) ⟹ P);
	interpret Ex (∃) :=
		discharge for α x, if ax: α.[x] then ∃x. α.[x] :=
			unfold ex_def;
			case for P, all: ∀x. α.[x] ⟹ P :=
				by all[OF ax];
			qed;
		discharge if ex: ∃x. α.[x] then (∀x. α.[x] ⟹ P) ⟹ P :=
			by ex[unfolded ex_def];
		end;
	end;

locale TwoValuedLambda :=
	import TwoValued;
	show eq_true: if P: P then P = true :=
		by imp_imp_eq[OF P true_intro];
	show true_eq: if P: P then true = P :=
		unfold eq_true[OF P];
		done;
	show eq_refl_eq_true: (x = x) = true :=
		by eq_true[OF eq.refl];
	show weaken_eq: (P ⟹ Q ⟹ P) = true :=
		by eq_true[OF weaken];
	show eq_true_iff: P = true ⟺ P :=
		apply iff_intro;
		case Pt: P = true :=
			unfold Pt;
			done;
		by eq_true;
	show true_eq_iff: true = P ⟺ P :=
		unfold(⟺) eq_iff.commute;
		by eq_true_iff;
	show imp_true_eq: (P ⟹ true) = true :=
		by eq_true[OF weaken[OF true_intro]];
	show true_and_true_eq: (true ∧ true) = true :=
		by eq_true[OF true_and_true];
	---
	Moreover, we assume that the following identity.
	---
	show true_imp_eq: (true ⟹ P) = P :=
		by imp_eq[OF true_intro];

	interpret imp: MetaLeftNeutral (⟹) true (=) :=
		discharge (true ⟹ P) = P :=
			apply+ imp_eq true_intro;
			qed;
		end;

	interpret imp: MetaRightAbsorb (⟹) true (=) :=
		discharge (P ⟹ true) = true :=
			apply+ eq_true;
			by weaken[OF true_intro];
		end;
	end;

locale TwoValuedNot :=
	fix false;
	import TwoValuedLambda;
	interpret DefineNot;
	show not_false_eq: (¬false) = true :=
		apply eq_true;
		by not_false;
	show not_true_eq: (¬true) = false :=
		unfold not_def;
		by true_imp_eq;
	end;
