-----
## Notions for Sets or Types
-----
import Base.
fix (∈).

begin

theory Member:
	fix x A.
	assume closed: x ∈ A.
end

theory SubEq:
	fix (⊆).
	assume elim1: if A ⊆ B then if x ∈ A then x ∈ B.
	assume intro: if ∀x. x ∈ A ⟹ x ∈ B then A ⊆ B.
begin
	interpret MetaPreorder (⊆);
		-; by intro.
		- for A B C if AB, BC;
			by intro BC[THEN elim1] AB[THEN elim1].
		.
end

theory Reflexive:
	fix A (≤).
	assume refl: if x ∈ A then x ≤ x.
end

theory Symmetric:
	fix A (=).
	assume sym: if x = y, x ∈ A, y ∈ A then y = x.
end

theory SemiAttractive:
	fix A (≤).
	assume attract: if x ≤ y, y ≤ x, y ≤ z, x ∈ A, y ∈ A, z ∈ A then x ≤ z.
end

theory DualAttractive:
	fix A (≤).
	assume dual_attract: if x ≤ y, y ≤ x, x ≤ z, x ∈ A, y ∈ A, z ∈ A then y ≤ z.
end

theory Attractive:
	import SemiAttractive.
	import DualAttractive.
end

theory Transitive:
	fix A (≤).
	assume trans: if x ≤ y, y ≤ z, x ∈ A, y ∈ A, z ∈ A then x ≤ z.
begin
	interpret Attractive;
		- for x y z if xy, yx, yz, !, !, !;
			by trans[OF xy yz].
		- for x y z if xy, yx, xz, !, !, !;
			by trans[OF yx xz].
		.
end

theory Preorder:
	fix A (≤).
	import Reflexive A (≤).
	import Transitive A (≤).
end

theory Tolerance:
	fix A (=).
	import Reflexive A (=).
	import Symmetric A (=).
end

theory PartialEquivalence:
	fix A (=).
	import Symmetric A (=).
	import Transitive A (=).
end

theory Equivalence:
	fix A (=).
	import Reflexive A (=).
	import Symmetric A (=).
	import Transitive A (=).
begin
	interpret Tolerance.
	interpret PartialEquivalence.
end

