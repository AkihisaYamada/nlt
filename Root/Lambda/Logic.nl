------
# Untyped Lambda Calculus

We axiomatize untyped lambda calculus, and define logical operations, and arrive at untyped multivalued intuitionistic logic.
------
base Lambda.
begin

----
## Defining Logical Constructs
----
define true := ∀P. P ⟹ P.
define false := ∀P. P.
define[not] ¬ P := P ⟹ false.
define[and] P ∧ Q := ∀R. (P ⟹ Q ⟹ R) ⟹ R.
define[iff] P ⟺ Q := (P ⟹ Q) ∧ (Q ⟹ P).
define[or] P ∨ Q := ∀R. (P ⟹ R) ⟹ (Q ⟹ R) ⟹ R.
define[ex] (∃) α := ∀P. (∀x. α.[x] ⟹ P) ⟹ P.

define[tall] (∀:) ι α := ∀x. ι x ⟹ α.[x].
define[tex] (∃:) ι α := ∀P. (∀x. α.[x] ⟹ ι x ⟹ P) ⟹ P.

define[neq] x ≠ y := ¬ x = y.

interpret TypeFreeIntuitionistic;
	retain true := true;
		unfold true_def.
	retain false := false;
		- if f: false;
			by f[unfolded false_def].
		.
	show: for P Q, if [P, Q] then P ∧ Q;
		apply eq_prop2[OF and_def],
		- for R, if PQR: P ⟹ Q ⟹ R;
			by PQR.
		.
	show: for P Q, if PQ: P ∧ Q then P;
		by eq_prop1[OF and_def][OF PQ].
	show: for P Q, if PQ: P ∧ Q then Q;
		by eq_prop1[OF and_def][OF PQ].

	show: for P, if nP: ¬P, [P] then false;
		by nP[unfolded not_def].
	show: for P, if nP: P ⟹ false then ¬P;
		by nP[folded not_def].

	show: for P Q, if PQ: P ⟹ Q, QP: Q ⟹ P then P ⟺ Q;
		apply eq_prop2[OF iff_def],
		unfold and_def,
		- for R, if imp: (P ⟹ Q) ⟹ (Q ⟹ P) ⟹ R;
			by imp[OF PQ QP].
		.
	show: for P Q, if PQ: P ⟺ Q then P ⟹ Q;
		apply PQ[unfolded iff_def and_def],
		- if PQ: P ⟹ Q;
			by PQ.
		.
	show: for P Q, if PQ: P ⟺ Q then Q ⟹ P;
		apply PQ[unfolded iff_def and_def],
		- if PQ: P ⟹ Q, QP: Q ⟹ P;
			by QP.
		.

	show: for P Q, if P: P then P ∨ Q;
		have 1: if PR: P ⟹ R, QR: Q ⟹ R then R;
			by PR[OF P].
		by eq_prop2[OF or_def 1].
	show: for P Q, if Q: Q then P ∨ Q;
		have 1: if PR: P ⟹ R, QR: Q ⟹ R then R;
			by QR[OF Q].
		by eq_prop2[OF or_def 1].
	show: for P Q, P ∨ Q ⟹ (∀R. (P ⟹ R) ⟹ (Q ⟹ R) ⟹ R);
		unfold or_def,
		apply imp.refl=.

	show: for x α, if ax: α.[x] then ∃x. α.[x];
		unfold ex_def,
		- for P, if all: ∀x. α.[x] ⟹ P;
			by all[OF ax].
		.
	show: for α, (∃x. α.[x]) ⟹ ∀P. (∀x. α.[x] ⟹ P) ⟹ P;
		unfold ex_def,
		apply imp.refl=.
	.

setup rewrite iff_elim1 iff_elim2 iff.refl iff.trans.
setup dual iff.sym.

interpret eq_iff: MetaCommutative (=) (⟺);
	show: for x y, x = y ⟺ y = x;
		apply iff_intro,
		- if xy: x = y;
			unfold xy.
		- if yx: y = x;
			unfold yx.
		.
	.

theorem russel_paradox: ¬(∀P. P ∨ ¬P);
	apply not_intro,
	- if or: ∀P. P ∨ ¬P;
		define R x := ¬ x x.
		have eq: R R = (¬ R R);
			by R_def.
		have Ror: R R ∨ ¬ R R;
			by or.
		apply or_elim[OF Ror],
		- if RR: R R;
			have nRR: ¬ R R;
				fold eq,
				by RR.
			by not_imp_false[OF nRR RR].
		- if nRR: ¬ R R;
			have RR: R R;
				unfold eq,
				by nRR.
			by not_imp_false[OF nRR RR].
		.
	.

define decided x := x ∨ ¬x.

namespace decided begin

interpret imp: Magma decided (⟹);
	show: for x y, if x: decided x, y: decided y then decided (x ⟹ y);
		unfold decided_def,
		apply or_elim[OF y[unfolded decided_def]],
		- by or_intro1.
		- if ny: ¬y;
			apply or_elim[OF x[unfolded decided_def]],
			- if [x];
				apply+ or_intro2 not_intro,
				- by not_imp_false[OF ny].
				.
			- if nx: ¬x;
				apply or_intro1[OF not_elim[OF nx]].
			.
		.
	.

interpret and: Magma decided (∧);
	show: for x y, decided x ⟹ decided y ⟹ decided (x ∧ y);
		unfold+ decided_def,
		- if x: x ∨ ¬x, y: y ∨ ¬y;
			apply or_elim[OF x],
			- if [x];
				apply or_elim[OF y],
				- by or_intro1 and_intro.
				- by or_intro2 nand_intro2.
				.
			- by or_intro2 nand_intro1.
			.
		.
	.

interpret iff: Magma decided (⟺);
	show: for x y, decided x ⟹ decided y ⟹ decided (x ⟺ y);
		unfold iff_def,
		by and.type imp.type.
	.

interpret or: Magma decided (∨);
	show: for x y, decided x ⟹ decided y ⟹ decided (x ∨ y);
		unfold decided_def,
		- if x: x ∨ ¬x, y: y ∨ ¬y;
			apply or_elim[OF x],
			- by or_intro1.
			- if [¬x];
				apply or_elim[OF y],
				- if [y];
					apply or_intro1,
					by or_intro2.
				- if [¬y];
					apply or_intro2,
					unfold(⟺) nor_iff,
					by and_intro.
				.
			.
		.
	.

interpret PropositionalClassical decided;
	show: decided true;
		by or_intro #unfold decided_def.
	show: decided false;
		by or_intro not_false #unfold decided_def.
	show: for x, decided x ⟹ decided (¬ x);
		unfold+ decided_def,
		by or_intro nnot_intro #elim or_elim.
	show: ∀P. (P ⟹ false) ⟹ decided P ⟹ ¬ P;
		by not_intro.
	show: for P, ¬ P ⟹ P ⟹ decided P ⟹ false;
		by not_imp_false(P).
	show: ∀P Q. P ⟹ Q ⟹ decided P ⟹ decided Q ⟹ P ∧ Q;
		by and_intro.
	show: ∀P Q. P ∧ Q ⟹ decided P ⟹ decided Q ⟹ P;
		by #elim and_elim.
	show: ∀P Q. P ∧ Q ⟹ decided P ⟹ decided Q ⟹ Q;
		by #elim and_elim.
	show: ∀P Q. (P ⟹ Q) ⟹ (Q ⟹ P) ⟹ decided P ⟹ decided Q ⟹ P ⟺ Q;
		by iff_intro.
	show: ∀P Q. (P ⟺ Q) ⟹ P ⟹ decided P ⟹ decided Q ⟹ Q;
		by #elim iff_elim.
	show: ∀P Q. (P ⟺ Q) ⟹ Q ⟹ decided P ⟹ decided Q ⟹ P;
		by #elim iff_elim.
	show: ∀P Q. P ⟹ decided P ⟹ decided Q ⟹ P ∨ Q;
		by or_intro.
	show: ∀P Q. Q ⟹ decided P ⟹ decided Q ⟹ P ∨ Q;
		by or_intro.
	show: ∀P Q. P ∨ Q ⟹ ∀ R. (P ⟹ R) ⟹ (Q ⟹ R) ⟹ decided P ⟹ decided Q ⟹ decided R ⟹ R;
		by #elim or_elim.
	show: false ⟹ ∀P. decided P ⟹ P;
		by #elim false_elim.
	show: for P, decided P ⟹ P ∨ ¬ P;
		unfold decided_def.
	.
end

thm decided.pierce_law.

lemma nnot_decided: ¬ ¬ decided x;
	unfold decided_def,
	by nnot_excluded_middle.

define taut x := true.

lemma taut! taut x;
	unfold taut_def.

interpret intuitionistic: TypedIntuitionisticLogic taut;
	show: ∀P. (P ⟹ false) ⟹ taut P ⟹ ¬ P;
		by not_intro.
	show: for P, ¬ P ⟹ P ⟹ taut P ⟹ false;
		by not_imp_false(P).
	- .
	- by and_intro.
	- by #elim and_elim.
	- by #elim and_elim.
	- .
	- by iff_intro.
	- by #elim iff_elim.
	- by #elim iff_elim.
	- .
	- by or_intro.
	- by or_intro.
	- by #elim or_elim.
	- .
	- by #unfold tall_def.
	- for x ι α, if tall: ∀y:ι. α.[y];
		by tall[unfolded tall_def].
	- .
	- for x α ι, if [α.[x], ι x, ∀y. ι y ⟹ taut α.[y]];
		unfold tex_def,
		- for P, if all: ∀z. α.[z] ⟹ ι z ⟹ P;
			by all(x).
		.
	- for ι α P, if ex: ∃x:ι. α.[x], imp: ∀x. α.[x] ⟹ ι x ⟹ P, [∀x. ι x ⟹ taut α.[x], taut P];
		apply ex[unfolded tex_def],
		- for x;
			by imp(x).
		.
	- by #elim false_elim.
	.

lemma neq_intro: if xyf: x = y ⟹ false then x ≠ y;
	unfold neq_def,
	apply not_intro,
	by xyf.

note neq_elim: eq_prop1[OF neq_def].

lemma neq_irrefl: ¬ x ≠ x;
	unfold neq_def,
	apply nnot_intro.

lemma neq_imp_false: if neq: x ≠ y, eq: x = y then false;
	by not_imp_false[OF neq[unfolded neq_def] eq].

lemma neq_refl_imp_false: if xx: x ≠ x then false;
	by neq_imp_false[OF xx eq.refl].

lemma true_neq_false: true ≠ false;
	apply neq_intro,
	- if tf: true = false then false;
		fold tf.
	.

---
### Unique Existence
---

binder ∃! 0 0.

define[ex1] (∃!) α := ∃x. α.[x] ∧ (∀y. α.[y] ⟹ x = y).

lemma ex1_intro: for x, if x: α.[x], 1: (∀y. α.[y] ⟹ x = y) then ∃!x. α.[x];
	unfold ex1_def,
	apply ex_intro1(x),
	apply and_intro,
	by x 1.

lemma ex1_elim:
	if ex1: ∃!x. α.[x], body: ∀x. α.[x] ⟹ (∀y. α.[y] ⟹ x = y) ⟹ P
	then P;
	obtain x where and: (α.[x]) ∧ (∀y. α.[y] ⟹ x = y);
		- for thesis;
			apply ex1[unfolded+ ex1_def ex_def](thesis)=.
		.
	have ax: α.[x];
		by and_elim1[OF and].
	have 1: ∀y. α.[y] ⟹ x = y;
		by and_elim2[OF and].
	by body[OF ax 1].

theory UniqueChoice:
	fix THE.
	assume ex1_imp_THE: (∃!x. P.[x]) ⟹ P.[THE x. P.[x]].
begin
	lemma ex1_imp_THE_eq: if ex1: ∃!y. P.[y], x: P.[x] then (THE y. P.[y]) = x;
		apply ex1_elim[OF ex1],
		- for z, if az: P.[z], 1: ∀y. P.[y] ⟹ z = y;
			have zx: z = x;
				by 1[OF x].
			have zT: z = (THE x. P.[x]);
				by 1[OF ex1_imp_THE[OF ex1]].
			by zx[unfolded zT].
		.
end

theory Choice:
	fix SOME.
	assume ex_imp_SOME: (∃x. P.[x]) ⟹ P.[SOME x. P.[y]].
end

end


