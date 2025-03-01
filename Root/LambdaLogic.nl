------
# Untyped Lambda Calculus

We axiomatize untyped lambda calculus, and define logical operations, and arrive at untyped multivalued intuitionistic logic.
------
base Lambda;
finalize;

----
## Defining Logical Constructs
----

define true := ∀P. P ⟹ P;
define false := ∀P. P;
define (not_def) ¬ P := P ⟹ false;
define (and_def) P ∧ Q := ∀R. (P ⟹ Q ⟹ R) ⟹ R;
define (iff_def) P ⟺ Q := (P ⟹ Q) ∧ (Q ⟹ P);
define (or_def) P ∨ Q := ∀ R. (P ⟹ R) ⟹ (Q ⟹ R) ⟹ R;
define (ex_def) (∃) α := (∀P. (∀x. α.[x] ⟹ P) ⟹ P);

interpret TypeFreeIntuitionistic :=
	substitute true :=
		unfold true_def;
		done;
	substitute false :=
		- for P, if f: false then P :=
			by f[unfolded false_def];
		done;

	- for P Q, if [P, Q] then P ∧ Q :=
		apply eq_prop2[OF and_def];
		- for R, if PQR: P ⟹ Q ⟹ R :=
			by PQR;
		done;
	- for P Q, if PQ: P ∧ Q then P :=
		by eq_prop1[OF and_def][OF PQ];
	- for P Q, if PQ: P ∧ Q then Q :=
		by eq_prop1[OF and_def][OF PQ];

	- for P, if nP: ¬P, [P] then false :=
		by nP[unfolded not_def];
	- for P, if nP: P ⟹ false then ¬P :=
		by nP[folded not_def];

	- for P Q, if PQ: P ⟹ Q, QP: Q ⟹ P then P ⟺ Q :=
		apply eq_prop2[OF iff_def];
		unfold and_def;
		- for R, if imp: (P ⟹ Q) ⟹ (Q ⟹ P) ⟹ R :=
			by imp[OF PQ QP];
		done;
	- for P Q, if PQ: P ⟺ Q then P ⟹ Q :=
		apply PQ[unfolded iff_def and_def];
		- if PQ: P ⟹ Q :=
			by PQ;
		done;
	- for P Q, if PQ: P ⟺ Q then Q ⟹ P :=
		apply PQ[unfolded iff_def and_def];
		- if PQ: P ⟹ Q, QP: Q ⟹ P :=
			by QP;
		done;

	- if P: P then P ∨ Q :=
		show 1: if PR: P ⟹ R, QR: Q ⟹ R then R :=
			by PR[OF P];
		by eq_prop2[OF or_def 1];
	- if Q: Q then P ∨ Q :=
		show 1: if PR: P ⟹ R, QR: Q ⟹ R then R :=
			by QR[OF Q];
		by eq_prop2[OF or_def 1];
	- if PQ: P ∨ Q, PR: P ⟹ R, QR: Q ⟹ R then R :=
		by eq_prop1[OF or_def PQ PR QR];

	- for α x, if ax: α.[x] then ∃x. α.[x] :=
		unfold ex_def;
		- for P, if all: ∀x. α.[x] ⟹ P :=
			by all[OF ax];
		done;
	- if ex: ∃x. α.[x] then (∀x. α.[x] ⟹ P) ⟹ P :=
		just ex[unfolded ex_def];
	done;

setup rewrite iff_elim1 iff_elim2 iff.refl iff.trans;
setup dual iff.sym;
setup cong iff_cong_imp iff_cong_iff iff_cong_and iff_cong_all;

interpret eq_iff: MetaCommutative (=) (⟺) :=
	- x = y ⟺ y = x :=
		apply iff_intro;
		- if xy: x = y :=
			unfold xy;
			done;
		- if yx: y = x :=
			unfold yx;
			done;
		done;
	done;

show russel_paradox: ¬(∀P. P ∨ ¬P) :=
	apply not_intro;
	- if or: ∀P. P ∨ ¬P :=
		define R x := ¬ x x;
		show eq: R R = (¬ R R) :=
			by R_def;
		show Ror: R R ∨ ¬ R R :=
			by or;
		apply or_elim[OF Ror];
		- if RR: R R :=
			show nRR: ¬ R R :=
				fold eq;
				by RR;
			by not_imp_false[OF nRR RR];
		- if nRR: ¬ R R :=
			show RR: R R :=
				unfold eq;
				by nRR;
			by not_imp_false[OF nRR RR];
		done;
	done;


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
	- if tf: true = false then false :=
		fold tf;
		done;
	done;


prefix ∃! 0 0;

define (ex1_def) (∃!) α := ∃x. α.[x] ∧ (∀y. α.[y] ⟹ x = y);

show ex1_intro: for x, if x: α.[x], 1: (∀y. α.[y] ⟹ x = y) then ∃!x. α.[x] :=
	unfold ex1_def;
	apply ex_intro1(x);
	apply and_intro;
	by x 1;

show ex1_elim:
	if ex1: ∃!x. α.[x], body: ∀x. α.[x] ⟹ (∀y. α.[y] ⟹ x = y) ⟹ P
	then P
:=
	obtain x where and: (α.[x]) ∧ (∀y. α.[y] ⟹ x = y) :=
		- for thesis :=
			just ex1[unfolded+ ex1_def ex_def];
		done;
	show ax: α.[x] :=
		by and_elim1[OF and];
	show 1: ∀y. α.[y] ⟹ x = y :=
		by and_elim2[OF and];
	by body[OF ax 1];



