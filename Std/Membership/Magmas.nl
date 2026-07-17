----
## Relation Symbol and Membership

Every binary symbol defines magma properties.
----
import base? Std.MetaRelation.

begin

theory LeftMonotone A B (*) :=
	assume left_mono: if y ⊏ y', x ∈ A, y ∈ B, y' ∈ B then x * y ⊏ x * y'.
end

theory RightMonotone A B (*) :=
	assume right_mono: if x ⊏ x', x ∈ A, x' ∈ A, y ∈ B then x * y ⊏ x' * y.
end

theory Monotone A (*) :=
	import LeftMonotone A A.
	import RightMonotone A A.
end

theory Compatible A (*) :=
	assume comp: if x ⊏ x', y ⊏ y', x ∈ A, y ∈ A, x' ∈ A, y' ∈ A then x * y ⊏ x' * y'.
begin
	lemma cong:
		if !x ∈ A, !y ∈ A, ! x ⊏ x', ! y ⊏ y', !x' ∈ A, !y' ∈ A then x * y ⊏ x' * y';
		apply comp.
end

theory Commutative A (*) :=
	assume commute: if x ∈ A, y ∈ A then x * y ⊏ y * x.
end

theory Idempotent A (*) :=
	assume idem: if x ∈ A then x * x ⊏ x.
end

theory LeftCancellative A B (*) :=
	assume left_cancels: if x * y ⊏ x * y', x ∈ A, y ∈ B, y' ∈ B then y ⊏ y'.
end

theory RightCancellative A B (*) :=
	assume right_cancels: if x * y ⊏ x' * y, x ∈ A, x' ∈ A, y ∈ B then x ⊏ x'.
end

theory LeftAssociative A B (*) (⋅) :=
	assume left_assoc: if x ∈ A, y ∈ A, z ∈ B then (x * y) ⋅ z ⊏ x ⋅ y ⋅ z.
end

theory RightAssociative A B (^) (*) :=
	assume right_assoc: if x ∈ A, y ∈ B, z ∈ B then x ^ (y * z) ⊏ x ^ y ^ z.
end

theory LeftDistributive A B (⋅) (+) (++) :=
	assume left_distrib: if x ∈ A, y ∈ B, z ∈ B then x ⋅ (y + z) ⊏ x ⋅ y ++ x ⋅ z.
end

theory RightDistributive A B (⋅) (+) (++) :=
	assume right_distrib: if x ∈ A, y ∈ A, z ∈ B then (x + y) ⋅ z ⊏ x ⋅ z ++ y ⋅ z.
end

theory Distributive A (*) (+) :=
	import LeftDistributive A A (*) (+) (+).
	import RightDistributive A A (*) (+) (+).
end

theory LeftAbsorb A (*) (0) :=
	assume left_absorb: if x ∈ A then 0 * x ⊏ 0.
end

theory RightAbsorb A (*) (0) :=
	assume right_absorb: if x ∈ A then x * 0 ⊏ 0.
end

theory LeftNeutral A (*) (1) :=
	assume left_neutral: if x ∈ A then 1 * x ⊏ x.
end

theory RightNeutral A (*) (1) :=
	assume right_neutral: if x ∈ A then x * 1 ⊏ x.
end

theory LeftCancel A B (*) (\) :=
	assume left_cancel: if x ∈ A, y ∈ B then x \ (x * y) ⊏ y.
end

theory RightCancel A B (*) (/) :=
	assume right_cancel: if x ∈ A, y ∈ B then (x * y) / y ⊏ x.
end

theory LeftInverse A (*) (1) inverse :=
	assume left_inverse: if x ∈ A then inverse x * x ⊏ 1.
end

theory RightInverse A (*) (1) inverse :=
	assume right_inverse: if x ∈ A then x * inverse x ⊏ 1.
end

theory CommMagma :=
	import Magma.
	import Commutative.
end

theory Action A B (∘) (⋅) :=
	import LeftAssociative A B (∘) (⋅).
	import comp: Magma A (∘).
	import app: Binary (⋅) A B B.
end

theory LeftModuloid A B (⋅) (+) (++) :=
	import LeftDistributive A B (⋅) (++) (++).
	import RightDistributive A B (⋅) (+) (++).
	import mul: Binary (⋅) A B B.
	import sadd: Magma A (+).
	import add: Magma B (++).
end

theory RightModuloid A B (⋅) (+) (++) :=
	import RightDistributive A B (⋅) (++) (++).
	import LeftDistributive A B (⋅) (+) (++).
	import mul: Binary (⋅) B A B.
	import sadd: Magma A (+).
	import add: Magma B (++).
end

theory Ringoid A (*) (+) :=
	import mul: Magma A (*).
	import add: Magma A (+).
	import Distributive A (*) (+).
begin
	interpret LeftModuloid A A (*) (+) (+);
		interpret sadd: Magma A (+);
			by add.closed.
		.
	interpret RightModuloid A A (*) (+) (+).
end

end

