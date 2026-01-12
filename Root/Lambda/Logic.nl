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
print.
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
	obtain false where false_elim: false ⟹ ∀P. P;
		- for thesis if assm;
			define false := ∀P. P.
			by assm[of false] #unfold false_def.
		.
	obtain (¬) where
		not_intro: (P ⟹ false) ⟹ ¬P,
		not_imp_false: ¬P ⟹ P ⟹ false;
		- for thesis if assm;
			define not P := P ⟹ false.
			by assm[of not] #unfold not_def.
		.
	obtain (∧) where
		and_intro: P ⟹ Q ⟹ P ∧ Q,
		and_elim1: P ∧ Q ⟹ P,
		and_elim2: P ∧ Q ⟹ Q;
		- for thesis if assm;
			define and P Q := ∀R. (P ⟹ Q ⟹ R) ⟹ R.
			by assm[of and] #unfold and_def.
		.
	obtain (∨) where
		or_intro1: P ⟹ P ∨ Q,
		or_intro2: ∀P Q. Q ⟹ P ∨ Q,
		or_elim: P ∨ Q ⟹ ∀R. (P ⟹ R) ⟹ (Q ⟹ R) ⟹ R;
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

