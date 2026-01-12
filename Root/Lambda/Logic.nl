------
# Type-Free Logic on Lambda Calculus

On top fo untyped lambda calculus we obtain logical operations, and arrive at untyped multivalued intuitionistic logic.
------
begin

----
## Obtaining Logical Constructs
----

interpret UnaryAbstraction;
	- for F P if assm: ∀f. (∀x. f x = F.[x]) ⟹ P then P;
		apply assm[of (λx. F.[x])];
		by #unfold beta.
	.

define true := ∀P. P ⟹ P.
define false := ∀P. P.
define[not] ¬ P := P ⟹ false.
define[and] P ∧ Q := ∀R. (P ⟹ Q ⟹ R) ⟹ R.
define[iff] P ⟺ Q := (P ⟹ Q) ∧ (Q ⟹ P).
define[or] P ∨ Q := ∀R. (P ⟹ R) ⟹ (Q ⟹ R) ⟹ R.
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

