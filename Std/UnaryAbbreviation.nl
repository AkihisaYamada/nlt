---
# Unary Abbreviation

For any term with a free variable `x`,
we assume one can introduce a symbol `f` such that `f x` is equal to the term.
---
import Eq.
assume abbrev: if ∀f. (∀x. f x = F.[x]) ⟹ P then P.

begin

obtain id where id_eq(simp) id x = x;
	- for thesis;
		apply abbrev[of (x. x)]>0.
	.

---
One can obtain the type-free existential quantifier as a unary abbreviation.
---
interpret Ex;
	obtain (∃) where
		ex_intro1: for x P if P.[x] then ∃x. P.[x],
		ex_elim: if ∃x. P.[x], ∀x. P.[x] ⟹ Q then Q;
		- for thesis if assm;
			apply abbrev[of (P. (∀Q. (∀x. P.[x] ⟹ Q) ⟹ Q))];
			- for (∃) if eq: ∀P. (∃) P = (∀ Q. (∀x. P.[x] ⟹ Q) ⟹ Q);
				apply assm[of (∃)];
				- for x P if Px: P.[x] then ∃x. P.[x];
					unfold eq;
					- for Q if imp: ∀x. P.[x] ⟹ Q then Q;
						by imp[OF Px].
					.
				- for P if ex: ∃x. P.[x];
					- for Q if imp: ∀x. P.[x] ⟹ Q then Q;
						apply ex[unfolded eq];
						by #elim imp.
					.
				.
			.
		.
	.

lemma ex_abbrev: ∃f. ∀x. f x = F.[x];
	apply ex_intro[OF abbrev].

interpret Ex1;
	obtain (∃!) where
		ex1_intro1: for x P if P.[x], ∀y. P.[y] ⟹ y = x then ∃!x. P.[x],
		ex1_elim: if ∃!x. P.[x], ∀x. P.[x] ⟹ (∀y. P.[y] ⟹ y = x) ⟹ Q then Q;
		- for thesis if assm;
			apply abbrev[of (P. ∀Q. (∀x. P.[x] ⟹ (∀y. P.[y] ⟹ y = x) ⟹ Q) ⟹ Q)];
			- for (∃!) if eq;
				apply assm[of (∃!)];
				- for x P if Px, imp_eq;
					unfold eq;
					- for Q if imp;
						by imp[of x] Px imp_eq.
					.
				- for P if ex1;
					apply ex1[unfolded eq]=.
				.
			.
		.
	.

obtain inj where
	inj_elim1: if inj f, f x = f y then x = y,
	inj_intro: if ∀x y. f x = f y ⟹ x = y then inj f;
	- for thesis if assm;
		apply abbrev[of (f. (∀x y. f x = f y ⟹ x = y))];
		- for inj if eq;
			apply assm[of inj];
			- for f;
				unfold eq.
			- for f;
				unfold eq.
			.
		.
	.

lemma id_inj: inj id;
	by inj_intro.

lemma inj_imp_ex1: if f: inj f then ∃!x'. f x' = f x;
	apply ex1_intro1[of x];
	by inj_elim1[OF f].

---
There exists an injection, as exemplified by `id`.
---
lemma ex_inj_inv: ∃f. ∃g. ∀x. g (f x) = x;
	apply ex_intro;
	- for thesis1 if assm1;
		apply assm1[of id];
		apply ex_intro;
		- for thesis2 if assm2;
			apply assm2[of id];
			- for x;
				simp.
			.
		.
	.

lemma ex_inj: ∃f. inj f;
	apply ex_intro;
	- for P if assm;
		apply assm[OF id_inj].
	.

---
Having operator `THE` allows one to pick an inverse of an injection.
---
theory The:
	import The.
begin
	lemma inj_imp_ex_inv: if f: inj f then ∃g. ∀x. g (f x) = x;
		apply ex_intro;
		- for thesis if assm;
			apply abbrev[of (y. THE z. f z = y)];
			- for g if eq;
				apply assm[of g];
				- for x;
					unfold eq;
					apply inj_elim1[OF f];
					apply ex1_imp_THE[of (z. f z = f x)];
					apply inj_imp_ex1[OF f].
				.
			.
		.
		--- obtain (∋) where
			Collect_has_intro: P x ⟹ Collect P ∋ x,
			Collect_has_elim1: Collect P ∋ x ⟹ P x;
			- for thesis if assm;
				apply Collect_inj[THEN inj_imp_ex_inv, THEN ex_elim];
				- for (∋) if eq;
					apply assm[of (∋)];
					- for P x;
						unfold eq.
					- for P x;
						unfold eq.
					.
				.
			. ---
end
