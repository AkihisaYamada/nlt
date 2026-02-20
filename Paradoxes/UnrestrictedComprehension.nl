---
# Unrestricted Comprehension is Inconsistent
---
import Iff.
fix (∈) _Collect.
assume in_Collect_iff: x ∈ {x. P.[x]} ⟺ P.[x].
begin

theorem inconsistent: P;-- Any term is provable
	have nRR: if RR: {x. x ∈ x ⟹ P} ∈ {x. x ∈ x ⟹ P} then P;
		by RR[unfold in_Collect_iff] RR.
	have RR: {x. x ∈ x ⟹ P} ∈ {x. x ∈ x ⟹ P};
		unfold in_Collect_iff;
		by nRR.
	by nRR[OF RR].

thy.
