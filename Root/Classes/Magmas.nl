----
### Properties for Binary Operators with respect to Binary Relations
----
fix (=).
begin

theory Compatible:
	fix A (*).
	assume cong: for x y, x = x' ⟹ y = y' ⟹ x ∈ A ⟹ y ∈ A ⟹ x' ∈ A ⟹ y' ∈ A ⟹ x * y = x' * y'.
end

theory Associative:
	fix A (*).
	assume assoc: x ∈ A ⟹ y ∈ A ⟹ z ∈ A ⟹ x * y * z = x * (y * z).
end

theory Commutative:
	fix A (*).
	assume commute: x ∈ A ⟹ y ∈ A ⟹ x * y = y * x.
end

theory LeftNeutral:
	fix A (*) (1).
	assume left_neutral: x ∈ A ⟹ 1 * x = x.
end

theory RightNeutral:
	fix A (*) (1).
	assume right_neutral: x ∈ A ⟹ x * 1 = x.
end

theory LeftCancel:
	fix A (*) (\).
	assume left_cancel: x ∈ A ⟹ y ∈ A ⟹ x \ (x * y) = y.
end

theory RightCancel:
	fix A (*) (/).
	assume right_cancel: x ∈ A ⟹ y ∈ A ⟹ (x * y) / y = x.
end

theory LeftQuasiGroup:
	import LeftCancel.
	import cancel: RightCancel A (\) (*).
end

theory RightQuasiGroup:
	import RightCancel.
	import cancel: LeftCancel A (/) (*).
end


theory LeftAbsorb:
	fix A (*) (0).
	assume left_absorb: x ∈ A ⟹ 0 * x = 0.
end

theory RightAbsorb:
	fix A (*) (0).
	assume right_absorb: x ∈ A ⟹ x * 0 = 0.
end

theory Semigroup:
	import Magma.
	import Associative.
end

theory CommMagma:
	import Magma.
	import Commutative.
end

theory CommSemigroup:
	import CommMagma.
	import Semigroup.
end

theory MagmaLeftNeutral:
	fix A (*) (1).
	import Magma.
	import neutral: Member (1) A.
	import LeftNeutral.
begin
	note! neutral.closed.
end

theory MagmaRightNeutral:
	fix A (*) (1).
	import Magma.
	import neutral: Member (1) A.
	import RightNeutral.
begin
	note! neutral.closed.
end

theory MagmaNeutral:
	import MagmaLeftNeutral.
	import MagmaRightNeutral.
end

theory Monoid:
	import MagmaNeutral.
	import Semigroup.
end

theory MagmaLeftAbsorb:
	fix A (*) (0).
	import Magma.
	import absorb: Member (0) A.
	import LeftAbsorb.
begin
	note! absorb.closed.
end

theory MagmaRightAbsorb:
	fix A (*) (0).
	import Magma.
	import absorb: Member (0) A.
	import RightAbsorb.
begin
	note! absorb.closed.
end

theory MagmaAbsorb:
	import MagmaLeftAbsorb.
	import MagmaRightAbsorb.
end

theory SemigroupAbsorb:
	import MagmaAbsorb.
	import Semigroup.
end

theory MonoidAbsorb:
	fix A (*) (0) (1).
	import SemigroupAbsorb.
	import Monoid.
end

context Transitive begin
	interpret Magmas (≤).

	theory CommMagmaNeutral:
		import MagmaLeftNeutral.
		import CommMagma.
	begin
		interpret MagmaNeutral;
			for x if ! x ∈ A then x * 1 ≤ x;
				have 1: x * 1 ≤ 1 * x;
					apply commute.
				apply trans[OF 1];
				apply left_neutral.
			.
	end

	theory CommMonoid:
		import CommMagmaNeutral.
		import CommSemigroup.
	begin
		interpret Monoid.
	end

	theory CommMagmaAbsorb:
		fix (*) (0).
		import CommMagma.
		import MagmaLeftAbsorb.
	begin
		interpret MagmaAbsorb;
			for x if !x ∈ A then x * 0 ≤ 0;
				have 1: x * 0 ≤ 0 * x;
					by commute.
				by trans[OF 1] left_absorb.
			.
	end

	theory CommSemigroupAbsorb:
		import CommMagmaAbsorb.
		import CommSemigroup.
	begin
		interpret SemigroupAbsorb.
	end

	theory CommMonoidAbsorb:
		fix (*) (0) (1).
		import CommMonoid.
		import CommMagmaAbsorb.
	begin
		interpret MonoidAbsorb.
	end
end
