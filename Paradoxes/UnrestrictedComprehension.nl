---
# Unrestricted Comprehension is Inconsistent
---
import Iff.
fix (∈) Collect.
syntax {_. _} := Collect.
assume in_Collect_iff: x ∈ {x. P.[x]} ⟺ P.[x].
begin

theorem inconsistent: false;-- Any term is provable
	have nRR: if RR: {x. x ∈ x ⟹ false} ∈ {x. x ∈ x ⟹ false} then false;
		by RR[unfold in_Collect_iff] RR.
	have RR: {x. x ∈ x ⟹ false} ∈ {x. x ∈ x ⟹ false};
		unfold in_Collect_iff;
		by nRR.
	by nRR[OF RR].

