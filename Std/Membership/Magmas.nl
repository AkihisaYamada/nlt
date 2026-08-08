----
## Relation Symbol and Membership

Every binary symbol defines magma properties.
----
fix (~).

begin

theory LeftMonotone A B (*) :=
	assume left_mono: if y ~ y', x ∈ A, y ∈ B, y' ∈ B then x * y ~ x * y'.
end

theory RightMonotone A B (*) :=
	assume right_mono: if x ~ x', x ∈ A, x' ∈ A, y ∈ B then x * y ~ x' * y.
end

theory Monotone A (*) :=
	import LeftMonotone A A.
	import RightMonotone A A.
end

theory Compatible A (*) :=
	assume comp: if x ~ x', y ~ y', x ∈ A, y ∈ A, x' ∈ A, y' ∈ A then x * y ~ x' * y'.
begin
	lemma cong:
		if !x ∈ A, !y ∈ A, ! x ~ x', ! y ~ y', !x' ∈ A, !y' ∈ A then x * y ~ x' * y';
		apply comp.
end

theory Commutative A (*) :=
	assume commute: if x ∈ A, y ∈ A then x * y ~ y * x.
end

theory Idempotent A (*) :=
	assume idem: if x ∈ A then x * x ~ x.
end

theory LeftCancellative A B (*) :=
	assume left_cancels: if x * y ~ x * y', x ∈ A, y ∈ B, y' ∈ B then y ~ y'.
end

theory RightCancellative A B (*) :=
	assume right_cancels: if x * y ~ x' * y, x ∈ A, x' ∈ A, y ∈ B then x ~ x'.
end

theory LeftAssociative A B (*) (⋅) :=
	assume left_assoc: if x ∈ A, y ∈ A, z ∈ B then (x * y) ⋅ z ~ x ⋅ y ⋅ z.
end

theory RightAssociative A B (^) (*) :=
	assume right_assoc: if x ∈ A, y ∈ B, z ∈ B then x ^ (y * z) ~ x ^ y ^ z.
end

theory LeftDistributive A B (⋅) (+) (++) :=
	assume left_distrib: if x ∈ A, y ∈ B, z ∈ B then x ⋅ (y + z) ~ x ⋅ y ++ x ⋅ z.
end

theory RightDistributive A B (⋅) (+) (++) :=
	assume right_distrib: if x ∈ A, y ∈ A, z ∈ B then (x + y) ⋅ z ~ x ⋅ z ++ y ⋅ z.
end

theory Distributive A (*) (+) :=
	import LeftDistributive A A (*) (+) (+).
	import RightDistributive A A (*) (+) (+).
end

theory LeftAbsorb A (*) (0) :=
	assume left_absorb: if x ∈ A then 0 * x ~ 0.
end

theory RightAbsorb A (*) (0) :=
	assume right_absorb: if x ∈ A then x * 0 ~ 0.
end

theory LeftNeutral A (*) (1) :=
	assume left_neutral: if x ∈ A then 1 * x ~ x.
end

theory RightNeutral A (*) (1) :=
	assume right_neutral: if x ∈ A then x * 1 ~ x.
end

theory LeftCancel A B (*) (\) :=
	assume left_cancel: if x ∈ A, y ∈ B then x \ (x * y) ~ y.
end

theory RightCancel A B (*) (/) :=
	assume right_cancel: if x ∈ A, y ∈ B then (x * y) / y ~ x.
end

theory LeftInverse A (*) (1) inverse :=
	assume left_inverse: if x ∈ A then inverse x * x ~ 1.
end

theory RightInverse A (*) (1) inverse :=
	assume right_inverse: if x ∈ A then x * inverse x ~ 1.
end

theory CommMagma :=
	import Magma, Commutative.
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
	instance LeftModuloid A A (*) (+) (+);
		interpret sadd: Magma A (+);
			by add.closed.
		.
	instance RightModuloid A A (*) (+) (+).
end

context Reflexive begin

	instance Magmas (⊑).

	extend Compatible begin

		instance Monotone A (*);
			- if 1: y ⊑ y', x! x ∈ A, ! y ∈ A, ! y' ∈ A then x * y ⊑ x * y';
				apply comp[OF refl[OF x] 1].
			- if 1: x ⊑ x', ! x ∈ A, ! x' ∈ A, y! y ∈ A then x * y ⊑ x' * y;
				apply comp[OF 1 refl[OF y]].
			.
	end

end

context Transitive begin

	instance Magmas (⊏).

	theory MonoMagma :=
		import Magma, Monotone.
	begin
		instance Compatible;
			- if x: x ⊏ x', y: y ⊏ y', ... then x * y ⊏ x' * y';
				.. ⊏ x' * y;
					apply right_mono[OF x].
				apply left_mono[OF y].
			.
	end

	theory CommMonoMagma :=
		import CommMagma.
		import LeftMonotone A A.
	begin
		instance MonoMagma;
			- if xx': x ⊏ x', ... for y if ... then x * y ⊏ x' * y;
				.. ⊏ y * x;
					apply commute.
				.. ⊏ y * x';
					apply left_mono[OF xx'].
				apply commute.
			.
	end

end

context PartialEquivalence begin

	instance Magmas (~).

	theory MagmaLeftNeutral (*) (1) :=
		import Magma.
		import neutral: Member (1) A.
		import LeftNeutral.
	begin
		note! neutral.closed.
		lemma right_neutral_is_neutral:
			if all: ∀x. x ∈ A ⟹ x * e ~ x, !e ∈ A then e ~ 1;
			.. ~ 1 * e;
				apply sym;
				by left_neutral.
			by all.
	end

	theory MagmaRightNeutral (*) (1) :=
		import Magma.
		import neutral: Member (1) A.
		import RightNeutral.
	begin
		note! neutral.closed.
		lemma left_neutral_is_neutral:
			if all: ∀x. x ∈ A ⟹ e * x ~ x, !e ∈ A then e ~ 1;
			.. ~ e * 1;
				apply sym;
				by right_neutral.
			by all.

	end

	theory MagmaNeutral :=
		import MagmaLeftNeutral, MagmaRightNeutral.
	end

	theory CommMagmaNeutral :=
		import MagmaLeftNeutral, CommMagma.
	begin
		instance MagmaNeutral;
			- for x if ! x ∈ A then x * 1 ~ x;
				.. ~ 1 * x;
					apply commute.
				apply left_neutral.
			.
	end

	theory Semigroup :=
		import Magma.
		import LeftAssociative A A (*) (*).
	begin
		instance RightAssociative A A (*) (*);
			- if ! x ∈ A, ! y ∈ A, ! z ∈ A;
				apply sym;
				apply left_assoc.
			.

	end

	theory CommSemigroup :=
		import CommMagma, Semigroup.
	end

	theory Monoid :=
		import MagmaNeutral, Semigroup.
	end

	theory CommMonoid :=
		import CommMagmaNeutral, CommSemigroup.
	begin
		instance Monoid.
	end

	theory MagmaLeftAbsorb (*) (0) :=
		import Magma.
		import absorb: Member (0) A.
		import LeftAbsorb.
	begin
		note! absorb.closed.
		lemma right_absorb_is_absorb: if eq: ∀x. x ∈ A ⟹ x * z ~ z, !z ∈ A then z ~ 0;
			.. ~ 0 * z;
				apply sym;
				by eq.
			by left_absorb.
	end

	theory MagmaRightAbsorb (*) (0) :=
		import Magma.
		import absorb: Member (0) A.
		import RightAbsorb.
	begin
		note! absorb.closed.
		lemma left_absorb_is_absorb: if eq: ∀x. x ∈ A ⟹ z * x ~ z, !z ∈ A then z ~ 0;
			.. ~ z * 0;
				apply sym;
				by eq.
			by right_absorb.
	end

	theory MagmaAbsorb :=
		import MagmaLeftAbsorb.
		import MagmaRightAbsorb.
	end

	theory CommMagmaAbsorb (*) (0) :=
		import CommMagma.
		import MagmaLeftAbsorb.
	begin
		instance MagmaAbsorb;
			- for x if !x ∈ A then x * 0 ~ 0;
				.. ~ 0 * x;
					by commute.
				by left_absorb.
			.
	end

	theory SemigroupAbsorb :=
		import MagmaAbsorb, Semigroup.
	end

	theory CommSemigroupAbsorb :=
		import CommMagmaAbsorb, CommSemigroup.
	begin
		instance SemigroupAbsorb.
	end

	theory MonoidAbsorb (*) (0) (1) :=
		import SemigroupAbsorb, Monoid.
	end

	theory CommMonoidAbsorb (*) (0) (1) :=
		import CommMonoid, CommMagmaAbsorb.
	begin
		instance MonoidAbsorb.
	end

	theory CommRingoid (*) (+) :=
		import mul: CommMagma A (*).
		import add: MonoMagma (+).
		import LeftDistributive A A (*) (+) (+).
	begin
		note! mul.closed add.closed.
		instance Ringoid;
			- if ! x ∈ A, ! y ∈ A, ! z ∈ A then (x + y) * z ~ x * z + y * z;
				.. ~ z * (x + y);
					apply mul.commute.
				.. ~ z * x + z * y;
					apply left_distrib.
				apply add.comp;
				- apply mul.commute.
				- apply mul.commute.
				.
			.
	end

	theory Semiring :=
		import Ringoid.
		import mul: Semigroup (*).
		import add: CommSemigroup (+).
	end

	theory CommSemiring :=
		import CommRingoid.
		import mul: CommSemigroup (*).
		import add: CommSemigroup (+).
	begin
		instance Semiring.
	end

	theory MagmaLeftCancel :=
		fix (*) (\).
		import Magma.
		import lcancel: Magma A (\).
		import lcancel: LeftMonotone A A (\).
		import LeftCancel A A.
	begin
		note! lcancel.closed.
		instance LeftCancellative A A;
			- if eq: x * y ~ x * y', ... then y ~ y';
				.. ~ x \ (x * y);
					apply sym;
					apply left_cancel;
					by closed lcancel.closed.
				.. ~ x \ (x * y');
					by lcancel.left_mono eq.
				by left_cancel.
			.
	end

	theory MagmaRightCancel :=
		fix (*) (/).
		import Magma.
		import rcancel: Magma A (/).
		import rcancel: RightMonotone A A (/).
		import RightCancel A A.
	begin
		note! rcancel.closed.
		instance RightCancellative A A;
			- for x y x' if eq: x * y ~ x' * y, ... then x ~ x';
				.. ~ x * y / y;
					apply sym;
					by right_cancel.
				.. ~ x' * y / y;
					by rcancel.right_mono eq.
				by right_cancel.
			.
	end

	theory LeftQuasiGroup :=
		import MagmaLeftCancel.
		import lcancel: LeftCancel A A (\) (*).
	end

	theory RightQuasiGroup :=
		import MagmaRightCancel.
		import rcancel: RightCancel A A (/) (*).
	end

	theory QuasiGroup :=
		import LeftQuasiGroup.
		import RightQuasiGroup.
	end

	theory LeftLoop :=
		fix (*) 1 (\).
		import MagmaNeutral.
		import LeftQuasiGroup.
	end

end
