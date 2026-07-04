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

theory Fun :=
	fix (fun).
	assume fun_app: for A if s ∈ A then (fun x. F.[x]) s = F.[s].
begin

	theory FunType :=
		import base.FunType.
		assume fun_in_type: if ∀x ∈ A. F.[x] ∈ B then (fun x. F.[x]) ∈ A → B.
	end

	theory DepFunType :=
		import base.DepFunType.
		assume fun_in_FunIn! if ∀x ∈ A. F.[x] ∈ B.[x] then (fun x. F.[x]) ∈ (FUN x ∈ A. B.[x]).
	begin

	end

end
