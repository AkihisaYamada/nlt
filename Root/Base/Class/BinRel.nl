fix A (≤).

begin

theory Reflexive:
	assume refl: x : A ⟹ x ≤ x.
end

theory Transitive:
	assume trans: x ≤ y ⟹ y ≤ z ⟹ x : A ⟹ y : A ⟹ z : A ⟹ x ≤ z.
end

theory Preorder:
	import Reflexive.
	import Transitive.
end

theory Symmetric:
	assume sym: x ≤ y ⟹ x : A ⟹ y : A ⟹ y ≤ x.
end

theory PartialEquivalence:
	import Symmetric.
	import Transitive.
end

theory Equivalence:
	import Symmetric.
	import Preorder.
begin
	interpret PartialEquivalence.
end



