---
# Equality and Membership
---
import base? Std.Membership.

begin

interpret eq: MetaEquivalence (=).--TODO: want "eq." for magmas?

theory Antisymmetric :=
	fix A (⊏).
	assume antisym: if x ⊏ y, y ⊏ x, x ∈ A, y ∈ A then x = y.
begin
	interpret Attractive;
		- if xy: x ⊏ y, yx: y ⊏ x, yz: y ⊏ z, x: x ∈ A, y: y ∈ A, z: z ∈ A then x ⊏ z;
			unfold antisym[OF xy yx x y];
			by yz.
		- if xy: x ⊏ y, yx: y ⊏ x, xz: x ⊏ z, x: x ∈ A, y: y ∈ A, z: z ∈ A then y ⊏ z;
			unfold antisym[OF yx xy y x];
			by xz.
		.
end

theory PseudoOrder :=
	import Reflexive.
	import Antisymmetric.
end

theory Order :=
	import Preorder.
	import Antisymmetric.
begin
	interpret PseudoOrder.
end

theory Injective f A :=
	assume injective: if x ∈ A, x' ∈ A, f x = f x' then x = x'.
end

theory Pair :=
	fix (,) fst snd.
	assume fst: if x ∈ A, y ∈ B then fst (x,y) = x.
	assume snd: if x ∈ A, y ∈ B then snd (x,y) = y.
end

