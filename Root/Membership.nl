-----
## Notions for Sets or Types
-----
import Base.
fix (∈).

begin

interpret in: MetaRelation (∈).

theory Member:
	fix x A.
	assume closed! x ∈ A.
end

theory Binder:
	fix ξ A B.
	assume closed: if ∀x. x ∈ A ⟹ F.[x] ∈ B then ξ A (x. F.[x]) ∈ B.
end

theory Unary:
	fix f A B.
	assume closed: if x ∈ A then f x ∈ B.
end

theory Fun:
	fix (→).
	assume fun_elim1: if f ∈ A → B, a ∈ A then f a ∈ B.
end

theory Binary:
	fix f A B C.
	assume closed: if x ∈ A, y ∈ B then f x y ∈ C.
end

theory Magma:
	fix A (*).
	import Binary (*) A A A.
begin
	note! closed.
end

theory SubsetEq:
	fix (⊆).
	assume subseteq_elim1: if A ⊆ B, x ∈ A then x ∈ B.
	assume subseteq_intro: if ∀x. x ∈ A ⟹ x ∈ B then A ⊆ B.
begin
	interpret MetaPreorder (⊆);
		- by subseteq_intro.
		- if AB: A ⊆ B, BC: B ⊆ C;
			by subseteq_intro BC[THEN subseteq_elim1] AB[THEN subseteq_elim1].
		.
end

theory Reflexive:
	fix A (≤).
	assume refl: if x ∈ A then x ≤ x.
begin
	interpret MetaRelation (≤).
end

theory Symmetric:
	fix A (=).
	assume sym: if x = y, x ∈ A, y ∈ A then y = x.
begin
	interpret MetaRelation (=).
end

theory SemiAttractive:
	fix A (≤).
	assume attract: if x ≤ y, y ≤ x, y ≤ z, x ∈ A, y ∈ A, z ∈ A then x ≤ z.
begin
	interpret MetaRelation (≤).
end

theory DualAttractive:
	fix A (≤).
	assume dual_attract: if x ≤ y, y ≤ x, x ≤ z, x ∈ A, y ∈ A, z ∈ A then y ≤ z.
begin
	interpret MetaRelation (≤).
end

theory Attractive:
	import SemiAttractive.
	import DualAttractive.
end

theory Transitive:
	fix A (≤).
	assume trans: if x ≤ y, y ≤ z, x ∈ A, y ∈ A, z ∈ A then x ≤ z.
begin
	interpret MetaRelation (≤).
	interpret Attractive;
		- if xy: x ≤ y, yx: y ≤ x, yz: y ≤ z, !, !, !;
			by trans[OF xy yz].
		- if xy: x ≤ y, yx: y ≤ x, xz: x ≤ z, !, !, !;
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

theory CollectRel:
	fix (<) CollectLt.
	assume Collect_intro: if x < a, P.[x] then x ∈ {x < a. P.[x]}.
	assume Collect_elim0: if x ∈ {x < a. P.[x]} then x < a.
	assume Collect_elim1: if x ∈ {x < a. P.[x]} then P.[x].
begin
	lemma Collect_elim: if x: x ∈ {x < a. P.[x]}, assm: x < a ⟹ P.[x] ⟹ Q then Q;
		apply assm[OF Collect_elim0[OF x] Collect_elim1[OF x]].
end

theory AllIn:
	import in: AllRel (∈) (∀∈).
end

theory CollectIn:
	import in: CollectRel (∈) CollectIn.
end