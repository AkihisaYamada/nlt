------
# Type-Free Lambda Calculus

This theory assumes the type-free β-rule and derive type-free intuitionistic logic.
------
import Eq.

fix (λ).
assume beta: (λx. Y.[x]) s = Y.[s].

begin

set define beta.

interpret UnaryAbbreviation;
	- for F P if assm: ∀f. (∀x. f x = F.[x]) ⟹ P then P;
		apply assm[of (λx. F.[x])];
		by #unfold beta.
	.

---
A pair `(x,y)` can be represented by `λf. f x y`. To distinguish pairs with those functions,
we wrap the functional representation by a newly obtained injection.
---
obtain pair_abs where ex_pair_case: ∃pair_case. ∀x. pair_case (pair_abs x) = x;
	apply ex_inj_inv[THEN ex_elim]>0=.

obtain pair_case where pair_case_abs: pair_case (pair_abs x) = x;
	apply ex_pair_case[THEN ex_elim]>0=.

interpret Pair;
	define[pair] (x,y) := pair_abs (λf. f x y).
	define fst p := pair_case p (λx y. x).
	define snd p := pair_case p (λx y. y).
	by #unfold pair_def fst_def snd_def pair_case_abs beta.

interpret Abbreviation;
	- for F P if assm: ∀f. (∀x y. f x y = F.[(x,y)]) ⟹ P then P;
		apply assm[of (λx y. F.[(x,y)])];
		by #unfold beta.
	.

interpret Collect;
	obtain Collect where ex_in: ∃(∈). ∀x P. x ∈ {x. P.[x]} ⟺ P.[x];
		- for thesis if assm;
			apply ex_inj_inv[THEN ex_elim];
			- for Collect if ex;
				obtain inv where inv: inv (Collect P) = P;
					apply ex[THEN ex_elim]=.
				apply assm[of Collect];
				apply abbrev2[of (p. (λ) (inv (snd p)) (fst p))];
				- for (∈) if (simp);
					apply ex_intro1[of (∈)];
					simp inv beta.
				.
			.
		.
	obtain (∈) where in_Collect_iff: x ∈ {x. P.[x]} ⟺ P.[x];
		apply ex_elim[OF ex_in]>0=.
	.

theory Ext:
	assume ext: if ∀x. Y.[x] = Z.[x] then (λx. Y.[x]) = (λx. Z.[x]).
begin

end

theory The:
	import The.
end

