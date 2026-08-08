---
It is convenient to "define" negation. However, without a two-valuedness assumption,
this formulation is strictly stronger than minimal negation.
---
fix false (¬).
assume not_eq_imp_false: (¬P) = (P ⟹ false).

begin

instance Std.Not.

instance MinimalNot;
	by #simp not_eq_imp_false.
