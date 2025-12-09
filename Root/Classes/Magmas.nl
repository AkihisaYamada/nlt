----
# Properties for Magmas
----
fix (=).
begin

theory Compatible:
	fix A (*).
	assume cong: for x y x' y'
		if x = x', y = y', x ∈ A, y ∈ A, x' ∈ A, y' ∈ A then x * y = x' * y'.
end

theory Associative:
	fix A (*).
	assume assoc: if x ∈ A, y ∈ A, z ∈ A then x * y * z = x * (y * z).
end

theory Commutative:
	fix A (*).
	assume commute: if x ∈ A, y ∈ A then x * y = y * x.
end

theory LeftCancellative:
	fix A (*).
	assume left_cancels: if x * y = x * y', x ∈ A, y ∈ A, y' ∈ A then y = y'.
end

theory RightCancellative:
	fix A (*).
	assume right_cancels: if x * y = x' * y, x ∈ A, x' ∈ A, y ∈ A then x = x'.
end

theory LeftAbsorb:
	fix A (*) (0).
	assume left_absorb: if x ∈ A then 0 * x = 0.
end

theory RightAbsorb:
	fix A (*) (0).
	assume right_absorb: if x ∈ A then x * 0 = 0.
end

theory LeftNeutral:
	fix A (*) (1).
	assume left_neutral: if x ∈ A then 1 * x = x.
end

theory RightNeutral:
	fix A (*) (1).
	assume right_neutral: if x ∈ A then x * 1 = x.
end

theory LeftCancel:
	fix A (*) (\).
	assume left_cancel: if x ∈ A, y ∈ A then x \ (x * y) = y.
end

theory RightCancel:
	fix A (*) (/).
	assume right_cancel: if x ∈ A, y ∈ A then (x * y) / y = x.
end

theory LeftInverse:
	fix A (*) (1) inverse.
	assume left_inverse: if x ∈ A then inverse x * x = 1.
end

theory RightInverse:
	fix A (*) (1) inv.
	assume right_inverse: if x ∈ A then x * inverse x = 1.
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

context PartialEquivalence begin

	interpret Magmas.

	theory MagmaLeftNeutral:
		fix (*) (1).
		import Magma.
		import neutral: Member (1) A.
		import LeftNeutral.
	begin
		note! neutral.closed.
		lemma right_neutral_is_neutral:
		if all: ∀x. x ∈ A ⟹ x * e = x, !e ∈ A then e = 1;
			have 1: e = 1 * e;
				apply sym;
				by left_neutral.
			have 2: 1 * e = 1;
				by all.
			by trans[OF 1 2].
	end

	theory MagmaRightNeutral:
		fix (*) (1).
		import Magma.
		import neutral: Member (1) A.
		import RightNeutral.
	begin
		note! neutral.closed.
		lemma left_neutral_is_neutral:
		if all: ∀x. x ∈ A ⟹ e * x = x, !e ∈ A then e = 1;
			have 1: e = e * 1;
				apply sym;
				by right_neutral.
			have 2: e * 1 = 1;
				by all.
			by trans[OF 1 2].
	end

	theory MagmaNeutral:
		import MagmaLeftNeutral.
		import MagmaRightNeutral.
	end

	theory CommMagmaNeutral:
		import MagmaLeftNeutral.
		import CommMagma.
	begin
		interpret MagmaNeutral;
			for x if ! x ∈ A then x * 1 = x;
				have 1: x * 1 = 1 * x;
					apply commute.
				apply trans[OF 1];
				apply left_neutral.
			.
	end

	theory Monoid:
		import MagmaNeutral.
		import Semigroup.
	end

	theory CommMonoid:
		import CommMagmaNeutral.
		import CommSemigroup.
	begin
		interpret Monoid.
	end

	theory MagmaLeftAbsorb:
		fix (*) (0).
		import Magma.
		import absorb: Member (0) A.
		import LeftAbsorb.
	begin
		note! absorb.closed.
		lemma right_absorb_is_absorb: if eq: ∀x. x ∈ A ⟹ x * z = z, !z ∈ A then z = 0;
			have 1: z = 0 * z;
				apply sym;
				by eq.
			have 2: 0 * z = 0;
				by left_absorb.
			by trans[OF 1 2].
	end

	theory MagmaRightAbsorb:
		fix (*) (0).
		import Magma.
		import absorb: Member (0) A.
		import RightAbsorb.
	begin
		note! absorb.closed.
		lemma left_absorb_is_absorb: if eq: ∀x. x ∈ A ⟹ z * x = z, !z ∈ A then z = 0;
			have 1: z = z * 0;
				apply sym;
				by eq.
			have 2: z * 0 = 0;
				by right_absorb.
			by trans[OF 1 2].
	end

	theory MagmaAbsorb:
		import MagmaLeftAbsorb.
		import MagmaRightAbsorb.
	end

	theory CommMagmaAbsorb:
		fix (*) (0).
		import CommMagma.
		import MagmaLeftAbsorb.
	begin
		interpret MagmaAbsorb;
			for x if !x ∈ A then x * 0 = 0;
				have 1: x * 0 = 0 * x;
					by commute.
				by trans[OF 1] left_absorb.
			.
	end

	theory SemigroupAbsorb:
		import MagmaAbsorb.
		import Semigroup.
	end

	theory CommSemigroupAbsorb:
		import CommMagmaAbsorb.
		import CommSemigroup.
	begin
		interpret SemigroupAbsorb.
	end

	theory MonoidAbsorb:
		fix (*) (0) (1).
		import SemigroupAbsorb.
		import Monoid.
	end

	theory CommMonoidAbsorb:
		fix (*) (0) (1).
		import CommMonoid.
		import CommMagmaAbsorb.
	begin
		interpret MonoidAbsorb.
	end

end

context Equivalence begin

	theory MagmaLeftCancel:
		fix (*) (\).
		import Magma.
		import lcancel: Magma A (\).
		import lcancel: Compatible A (\).
		import LeftCancel.
	begin
		note! lcancel.closed.
		interpret LeftCancellative;
			for x y y' if eq: x * y = x * y', !x ∈ A, !y ∈ A, !y' ∈ A then y = y';
				have 1: y = x \ (x * y);
					apply sym;
					apply left_cancel;
					by closed lcancel.closed.
				apply trans[OF 1];
				have 2: x \ (x * y) = x \ (x * y');
					by lcancel.cong eq refl.
				apply trans[OF 2];
				by left_cancel.
			.
	end

	theory MagmaRightCancel:
		fix (*) (/).
		import Magma.
		import rcancel: Magma A (/).
		import rcancel: Compatible A (/).
		import RightCancel.
	begin
		note! rcancel.closed.
		interpret RightCancellative;
			for x y x' if eq: x * y = x' * y, !, !, ! then x = x';
				have 1: x = x * y / y;
					apply sym;
					by right_cancel.
				apply trans[OF 1];
				have 2: x * y / y = x' * y / y;
					by rcancel.cong eq refl.
				apply trans[OF 2];
				by right_cancel.
			.
	end

	theory LeftQuasiGroup:
		import MagmaLeftCancel.
		import lcancel: LeftCancel A (\) (*).
	begin
--		interpret lcancel: MagmaLeftCancel (\) (*).
		thy.
	end

	theory RightQuasiGroup:
		import MagmaRightCancel.
		import rcancel: RightCancel A (/) (*).
	begin
--		interpret rcancel: MagmaRightCancel (/) (*).
		thy.
	end

	theory QuasiGroup:
		import LeftQuasiGroup.
		import RightQuasiGroup.
	end

	theory LeftLoop:
		fix (*) 1 (\).
		import MagmaNeutral.
		import LeftQuasiGroup.
	begin
	end

end
