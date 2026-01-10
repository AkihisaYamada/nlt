------
# Type-Free Logic on Lambda Calculus

On top fo untyped lambda calculus we define logical operations, and arrive at untyped multivalued intuitionistic logic.
------
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
define[ex] (∃) P := ∀P. (∀x. P.[x] ⟹ Q) ⟹ Q.
define[neq] x ≠ y := ¬ x = y.

interpret Intuitionistic;
	- true;
		unfold true_def.
	note(unfold) and_def not_def.
	- for P Q if PQ: P ⟹ Q, QP: Q ⟹ P then P ⟺ Q;
		unfold iff_def and_def;
		- for R if imp: (P ⟹ Q) ⟹ (Q ⟹ P) ⟹ R;
			by imp[OF PQ QP].
		.
	- for P Q if PQ: P ⟺ Q then P ⟹ Q;
		apply PQ[unfolded iff_def and_def].
	- for P Q if PQ: P ⟺ Q then Q ⟹ P;
		apply PQ[unfolded iff_def and_def].

	- for P Q if P: P then P ∨ Q;
		unfold or_def;
		- for R if PR: P ⟹ R, QR: Q ⟹ R then R;
			by PR[OF P].
		.
	- for P Q if Q: Q then P ∨ Q;
		unfold or_def;
		- for R if PR: P ⟹ R, QR: Q ⟹ R then R;
			by QR[OF Q].
		.
	- for P Q, P ∨ Q ⟹ (∀R. (P ⟹ R) ⟹ (Q ⟹ R) ⟹ R);
		unfold or_def;
		apply imp.refl=.

	- for x P if Px: P.[x] then ∃x. P.[x];
		unfold ex_def;
		for Q if all: ∀x. P.[x] ⟹ Q;
			by all[OF Px].
		.
	for P, (∃x. P.[x]) ⟹ ∀Q. (∀x. P.[x] ⟹ Q) ⟹ Q;
		unfold ex_def;
		apply imp.refl=.
	- if f: false then ∀P. P;
		by f[unfolded false_def].
	.
--

lemma eq_imp_iff(cong): if PQ: P = Q then P ⟺ Q;
	unfold(=) PQ.

namespace iff begin

	interpret ..iff.

	interpret eq: MetaCommutative (=);
		by iff_intro[OF eq.sym eq.sym].

end

theorem russel_paradox: ¬(∀P. P ∨ ¬P);
	apply not_intro;
	if or: ∀P. P ∨ ¬P;
		define R x := ¬ x x.
		have eq: R R = (¬ R R);
			by R_def.
		have Ror: R R ∨ ¬ R R;
			by or.
		apply or_elim[OF Ror];
		if RR: R R;
			have nRR: ¬ R R;
				fold(=) eq;
				by RR.
			by not_imp_false[OF nRR RR].
		if nRR: ¬ R R;
			have RR: R R;
				unfold eq;
				by nRR.
			by not_imp_false[OF nRR RR].
		.
	.
--

interpret UnaryAbbreviation;
	- for F P if assm: ∀f. (∀x. f x = F.[x]) ⟹ P then P;
		apply assm[of (λx. F.[x])];
		by beta.
	.

theory If:
	import If.
end

theory Choice:
	assume choice: (∀x. ∃y. P x y) ⟹ ∃f. ∀x. P x (f x).
end

theory ChoiceOperator:
	fix (SOME).
	assume ex_imp_SOME: (∃x. P.[x]) ⟹ P.[SOME x. P.[y]].
end

theory Collect:
	fix (∈) Collect.
	import Classes.
	assume in_Collect_iff: x ∈ Collect P ⟺ P x.
end

-- TODO: should have mutual obtain
define [in] x ∈ Y := Y x.
define Collect P := P.

interpret Collect;
	by #unfold in_def Collect_def.

define[empty] ∅ := Collect (λx. false).

define Singleton x := Collect (λy. y = x).

define[cup] X ∪ Y := Collect (λx. x ∈ X ∨ x ∈ Y).

set set_comprehension Collect (λ) ∅ Singleton (∪).

define UNIV := {x. true}.

lemma in_UNIV! x ∈ UNIV;
	unfold UNIV_def in_Collect_iff beta.

define[ball] (∀∈) X P := ∀x. x ∈ X ⟹ P.[x].
define[bex] (∃∈) X P := ∃x. x ∈ X ∧ P.[x].

define[subseteq] X ⊆ Y := ∀x ∈ X. x ∈ Y.

define[bigcap] ⋂XX := {x. ∀X ∈ XX. x ∈ X}.
define[bigcup] ⋃XX := {x. ∃X ∈ XX. x ∈ X}.

define DECIDED := {x. x ∨ ¬x}.

lemma in_DECIDED_iff: P ∈ DECIDED ⟺ P ∨ ¬P;
	unfold DECIDED_def in_Collect_iff beta.

namespace DECIDED begin

	interpret Prop (∈) DECIDED;
	- for x y if x: x ∈ DECIDED, y: y ∈ DECIDED then (x ⟹ y) ∈ DECIDED;
		unfold in_DECIDED_iff;
		apply or_elim[OF y[unfolded in_DECIDED_iff]];
		-; by or_intro1.
		- if ny: ¬y;
			apply or_elim[OF x[unfolded in_DECIDED_iff]];
			- if !x;
				apply+ or_intro2 not_intro;
				by not_imp_false[OF ny].
			- if nx: ¬x;
				apply or_intro1[OF not_elim[OF nx]].
			.
		.
	.

	interpret Classical;
		note! not_intro and_intro or_intro iff_intro.
		note #elim: and_elim or_elim iff_elim false_elim.

	- false ∈ DECIDED;
		by not_false #unfold in_DECIDED_iff.
	- for x, x ∈ DECIDED ⟹ (¬ x) ∈ DECIDED;
		by nnot_intro #unfold in_DECIDED_iff.
		show and_type: for x y, x ∈ DECIDED ⟹ y ∈ DECIDED ⟹ (x ∧ y) ∈ DECIDED;
			unfold+ in_DECIDED_iff;
			if x: x ∨ ¬x, y: y ∨ ¬y;
				apply or_elim[OF x];
				if !x;
					apply or_elim[OF y];
					- by or_intro1 and_intro.
					by or_intro2 nand_intro2.
				by or_intro2 nand_intro1.
			.
	- for x y, x ∈ DECIDED ⟹ y ∈ DECIDED ⟹ (x ∨ y) ∈ DECIDED;
		unfold+ in_DECIDED_iff;
		- if x: x ∨ ¬x, y: y ∨ ¬y;
			apply or_elim[OF x];
			-; by or_intro1.
			- if ! ¬x;
				apply or_elim[OF y];
				- if ! y;
					apply or_intro1;
					by or_intro2.
				- if ! ¬y;
					apply or_intro2;
					unfold nor_iff;
					by and_intro.
				.
			.
		.
	- for x y, x ∈ DECIDED ⟹ y ∈ DECIDED ⟹ (x ⟺ y) ∈ DECIDED;
		unfold iff_def;
		by and_type imp_type.
	- for P if P0: P ⟹ false, _ then ¬ P;
		by P0.
	- for P, ¬ P ⟹ P ⟹ P ∈ DECIDED ⟹ false;
		by #elim not_imp_false.
	retain true := true;
		by or_intro #unfold in_DECIDED_iff.
	-  for P, P ∈ DECIDED ⟹ P ∨ ¬ P;
		unfold in_DECIDED_iff.
	.

end

thm DECIDED.pierce_law.

lemma nnot_DECIDED: ¬ ¬ x ∈ DECIDED;
	unfold in_DECIDED_iff;
	by nnot_excluded_middle.



define [fun] (A → B) := {f. ∀x. x ∈ A ⟹ f x ∈ B}.

namespace UNIV begin

	note(unfold) ball_def.

	interpret HOL (∈) UNIV UNIV;
		- for x P A if !P.[x], !, !, !;
			unfold bex_def;
			- for Q if all: ∀z. z ∈ A ⟹ P.[z] ⟹ Q;
				by all[of x].
			.
		- for P A if ex: ∃x ∈ A. P.[x];
			- for Q if imp: ∀x. x ∈ A ⟹ P.[x] ⟹ Q;
				apply ex[unfolded bex_def];
				- for x;
					by imp[of x].
				.
			.
		- for f A B if f: f ∈ A → B, !, ! then ∀a. a ∈ A ⟹ f a ∈ B;
			by f[unfolded fun_def in_Collect_iff beta].
		.

	interpret Intuitionistic;
		note! or_intro iff_intro.
		note(elim) or_elim iff_elim.
		retain false;
			by #elim false_elim.
		- for P if ! P ⟹ false, ! P ∈ UNIV then ¬ P;
			by not_intro.
		- for P, ¬ P ⟹ P ⟹ P ∈ UNIV ⟹ false;
			by not_imp_false[of P].
		.
end

lemma neq_intro: if xyf: x = y ⟹ false then x ≠ y;
	unfold neq_def;
	apply not_intro;
	by xyf.

note neq_elim: eq_imp[OF neq_def].

lemma neq_irrefl: ¬ x ≠ x;
	unfold neq_def;
	apply nnot_intro.

lemma neq_imp_false: if neq: x ≠ y, eq: x = y then false;
	by not_imp_false[OF neq[unfolded neq_def] eq].

lemma neq_refl_imp_false: if xx: x ≠ x then false;
	by neq_imp_false[OF xx eq.refl].

lemma true_neq_false: true ≠ false;
	apply neq_intro;
	- if tf: true = false then false;
		fold tf.
	.

define connex A (≤) := ∀x ∈ A. ∀y ∈ A. x ≤ y ∨ y ≤ x.

theory Connex A (≤):
	assume connex: connex A (≤).
begin
	lemma comparable: if !x ∈ A, !y ∈ A then x ≤ y ∨ y ≤ x;
		by connex[unfolded connex_def].
end

define monotone A (≤) f := ∀x ∈ A. ∀y ∈ A. x ≤ y ⟹ f x ≤ f y.
define upper_bound X (≤) y := ∀x ∈ X. x ≤ y.
define lower_bound x (≤) Y := ∀y ∈ Y. x ≤ y.

define supremum A (≤) X s := lower_bound s (≤) {b. b ∈ A ∧ upper_bound X (≤) b}.

define well_relation A (≤) := ∀X. X ≠ {} ⟹ X ⊆ A ⟹ ∃e ∈ X. lower_bound e (≤) X.

theory WellRelation:
	fix A (≤).
	assume well_relation: well_relation A (≤).
begin
	lemma ex_extreme: if X0: X ≠ {}, XA: X ⊆ A then ∃e ∈ X. lower_bound e (≤) X;
		by well_relation[unfolded well_relation_def, OF X0 XA].
end

theory PreWellRelation:
	import SemiAttractive.
	import WellRelation.
begin

end

define well_order A (≤) :=


define well_complete A (≤) := ∀X. X ⊆ A ⟹ well_relation A (≤) ⟹ ∃s. supremum A (≤) X s.

define fp_derivation A (≤) f X :=
	X ⊆ A ∧ 

theory WellComplete:
	fix A (≤).
	assume well_complete: well_complete A (≤).
begin
	define 
	lemma mono_imp_ex_fixed_point:
		if mono: monotone f A (≤), f: f ∈ A → A then ∃p ∈ A. f p = p;
		apply ex_intro[of ];

end

end


