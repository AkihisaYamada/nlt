---
### Minimal Not via Free False

Having `(⟺)` primitive makes the following formulation of minimal negation is convenient.
---

fix false (¬).

assume not_iff_imp_false: ¬P ⟺ (P ⟹ false).

begin

interpret Not.

interpret MinimalNot;
	by #simp not_iff_imp_false.

context Not.MinimalNot begin

	interpret True.

	interpret not_true: FalseNot (¬true);
		by not_iff_imp_not.

end
