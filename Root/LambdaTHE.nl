---
# Logic obtained by `λ` and `THE`

The combination the `λ` and `THE` operators is sufficient to start mathematics.
---
import Lambda.
import The.

begin

---
First we obtain if-then-else.
---
interpret If;
	obtain If where
		If_then: if P then If P x y = x,
		If_else: if P ⟹ x = y then If P x y = y;
		- for thesis if assm;
			define If P x y := THE z. ∀Q. ((P ⟹ z = x) ⟹ ((P ⟹ x = y) ⟹ z = y) ⟹ Q) ⟹ Q.
			apply assm[of If];
			- for P x y if P: P then If P x y = x;
				unfold If_def;
				apply THE_eq_intro;
				-; apply ex1_intro1[of x];
					- for Q if assm2;
						by assm2 P.
					- for z if elim;
						apply elim;
						by P.
					.
				- for Q if assm2;
					by assm2 P.
				.
			- for P x y if nP: P ⟹ x = y then If P x y = y;
				unfold If_def;
				apply THE_eq_intro;
				-; apply ex1_intro1[of y];
					- for Q if assm2;
						apply assm2;
						by #unfold nP.
					- for z if elim;
						apply elim;
						- if 1: P ⟹ z = x, 2: (P ⟹ x = y) ⟹ z = y then z = y;
							by 2 nP.
						.
					.
				- for Q if assm2;
					by assm2 #unfold nP.
				.
			.
		.
	.
---
This yields the pair constructor `(,)` and projections.
---
interpret Abbreviation;
	- for F Q if assm: ∀f'. (∀ x y. f' x y = F.[(x, y)]) ⟹ Q then Q;
		apply assm[of (λx y. F.[(x,y)])];
		- for x y;
			unfold beta.
		.
	.

interpret The.