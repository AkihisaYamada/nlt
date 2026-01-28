------
# Type-Free Lambda Calculus
------
import Eq.

fix (λ).
assume beta: (λx. Y.[x]) s = Y.[s].

begin

set define beta.

----
## Obtaining Logical Constructs

The untyped β-axiom is enough to derive intuitionistic logic.
----

interpret UnaryAbstraction;
	- for F P if assm: ∀f. (∀x. f x = F.[x]) ⟹ P then P;
		apply assm[of (λx. F.[x])];
		by #unfold beta.
	.

interpret Iff;
	obtain (⟺) where
		iff_intro: (P ⟹ Q) ⟹ (Q ⟹ P) ⟹ P ⟺ Q,
		iff_elim1: (P ⟺ Q) ⟹ P ⟹ Q,
		iff_elim2: (P ⟺ Q) ⟹ Q ⟹ P;
		- for thesis if assm;
			define[iff] P ⟺ Q := ∀R. ((P ⟹ Q) ⟹ (Q ⟹ P) ⟹ R) ⟹ R.
			apply assm[of (⟺)];
			- for P Q if PQ, QP;
				unfold iff_def;
				- for R if assm2;
					apply assm2[OF PQ QP].
				.
			- for P Q if iff;
				apply iff[unfolded iff_def].
			- for P Q if iff;
				apply iff[unfolded iff_def].
			.
		.
	.

interpret Intuitionistic;
	note(cong) eq_imp_iff.
	obtain true where true_intro: true;
		- for thesis if assm;
			define true := ∀P. P ⟹ P.
			by assm[of true] #unfold true_def.
		.
	obtain false where false_elim: if false then P;
		- for thesis if assm;
			define false := ∀P. P.
			by assm[of false] #unfold false_def.
		.
	obtain (¬) where
		not_intro: if P ⟹ false then ¬P,
		not_imp_false: if ¬P, P then false;
		- for thesis if assm;
			define not P := P ⟹ false.
			by assm[of not] #unfold not_def.
		.
	obtain (∧) where
		and_intro: if P, Q then P ∧ Q,
		and_elim1: if P ∧ Q then P,
		and_elim2: if P ∧ Q then Q;
		- for thesis if assm;
			define and P Q := ∀R. (P ⟹ Q ⟹ R) ⟹ R.
			by assm[of and] #unfold and_def.
		.
	obtain (∨) where
		or_intro1: for P Q if P then P ∨ Q,
		or_intro2: for P Q if Q then P ∨ Q,
		or_elim: if P ∨ Q, P ⟹ R, Q ⟹ R then R;
		- for thesis if assm;
			define or P Q := ∀R. (P ⟹ R) ⟹ (Q ⟹ R) ⟹ R.
			apply assm[of or];
			- for P Q if P;
				unfold or_def;
				- for R if PR, QR;
					by PR[OF P].
				.
			- for P Q if Q;
				unfold or_def;
				- for R if PR, QR;
					by QR[OF Q].
				.
			- for P Q if or;
				- for R;
					apply or[unfolded or_def]=.
				.
			.
		.
	.


theory Ext:
	assume ext: if ∀x. Y.[x] = Z.[x] then (λx. Y.[x]) = (λx. Z.[x]).
end

theory If:
	import If.
begin
	interpret Pair;
		define[pair] (x,y) P := (If P x y).
		define fst xy := xy (∀P. P ⟹ P).
		define snd xy := xy (∀P. P).
	- for x y, fst (x,y) = x;
		by If_then #unfold fst_def pair_def.
	- for x y, snd (x,y) = y;
		by If_else #unfold snd_def pair_def.
	.
end

