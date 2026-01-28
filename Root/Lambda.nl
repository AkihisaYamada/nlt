------
# Type-Free Lambda Calculus
------
import Eq.

fix (λ).
assume beta: (λx. Y.[x]) s = Y.[s].

begin

set define beta.

----
The untyped β-axiom is enough to derive intuitionistic logic.
----
print.

interpret Pair;
	define[pair] (x,y) f := f x y.
	define fst p := p (λx y. x).
	define snd p := p (λx y. y).
	by #unfold pair_def fst_def snd_def beta.

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

