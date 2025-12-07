----
### Properties for Binary Operators with respect to Binary Relations
----
context Relation begin

theory Compatible:
	fix (*).
	assume cong: for x y, x ≤ x' ⟹ y ≤ y' ⟹ x ∈ A ⟹ y ∈ A ⟹ x' ∈ A ⟹ y' ∈ A ⟹ x * y ≤ x' * y'.
end

theory Associative:
	fix (*).
	assume assoc: x ∈ A ⟹ y ∈ A ⟹ z ∈ A ⟹ x * y * z ≤ x * (y * z).
end

theory Commutative:
	fix (*).
	assume commute: x ∈ A ⟹ y ∈ A ⟹ x * y ≤ y * x.
end

theory LeftNeutral:
	fix (*) (1).
	assume left_neutral: x ∈ A ⟹ 1 * x ≤ x.
end

theory RightNeutral:
	fix (*) (1).
	assume right_neutral: x ∈ A ⟹ x * 1 ≤ x.
end

theory LeftAbsorb:
	fix (*) (0).
	assume left_absorb: x ∈ A ⟹ 0 * x ≤ 0.
end

theory RightAbsorb:
	fix (*) (0).
	assume right_absorb: x ∈ A ⟹ x * 0 ≤ 0.
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
	fix (*) (1).
	import Magma.
	import neutral: Member (1) A.
	import LeftNeutral.
begin
	note! neutral.closed.
end

theory MagmaRightNeutral:
	fix (*) (1).
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
	fix (*) (0).
	import Magma.
	import absorb: Member (0) A.
	import LeftAbsorb.
begin
	note! absorb.closed.
end

theory MagmaRightAbsorb:
	fix (*) (0).
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
	fix (*) (0) (1).
	import SemigroupAbsorb.
	import Monoid.
end

context Transitive begin

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
	end

	theory CommMonoidAbsorb:
		fix (*) (0) (1).
		import CommMonoid.
		import CommMagmaAbsorb.
	end

end

end