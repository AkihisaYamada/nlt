----
## Magma Properties

Any pair of a membership and equality defines magma properties.
----
fix (~) (∈).

begin

instance Membership.

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
		if [x ∈ A, y ∈ A, x ~ x', y ~ y', x' ∈ A, y' ∈ A] then x * y ~ x' * y';
		apply comp.
end

theory Commutative A (*) :=
	assume commute: if x ∈ A, y ∈ A then x * y ~ y * x.
end

theory Idempotent A (*) :=
	assume idem: if x ∈ A then x * x ~ x.
end

theory LeftCancellative A B (*) :=
	assume left_cancels: for x if x * y ~ x * y', x ∈ A, y ∈ B, y' ∈ B then y ~ y'.
end

theory RightCancellative A B (*) :=
	assume right_cancels: for y if x * y ~ x' * y, x ∈ A, x' ∈ A, y ∈ B then x ~ x'.
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

theory LeftInverse A (*) 1 inverse :=
	assume left_inverse: if x ∈ A then inverse x * x ~ 1.
end

theory RightInverse A (*) 1 inverse :=
	assume right_inverse: if x ∈ A then x * inverse x ~ 1.
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
			- if 1: y ⊑ y', x! x ∈ A, [y ∈ A, y' ∈ A] then x * y ⊑ x * y';
				apply comp[OF refl[OF x] 1].
			- if 1: x ⊑ x', [x ∈ A, x' ∈ A], y! y ∈ A then x * y ⊑ x' * y;
				apply comp[OF 1 refl[OF y]].
			.
	end

end

context Transitive begin

	instance Magmas (⊏).

	extend Magma begin

		extend Monotone begin
			instance Compatible;
				- if x: x ⊏ x', y: y ⊏ y', ... then x * y ⊏ x' * y';
					.. ⊏ x' * y;
						apply right_mono[OF x].
					apply left_mono[OF y].
				.
		end

		extend Commutative begin
			theory Monotone :=
				import LeftMonotone A A.
			begin
				instance Magma.Monotone;
					- if xx': x ⊏ x', ... for y if ... then x * y ⊏ x' * y;
						.. ⊏ y * x;
							apply commute.
						.. ⊏ y * x';
							apply left_mono[OF xx'].
						apply commute.
					.
			end
		end

	end

end

context PartialEquivalence begin

	instance Magmas (~).

	extend Transitive.Magma begin

		theory LeftNeutral 1 :=
			import neutral: Member 1 A.
			import Magmas.LeftNeutral A (*) 1.
		begin
			note! neutral.closed.
			lemma right_neutral_is_neutral:
				if all: ∀x. x ∈ A ⟹ x * e ~ x, [e ∈ A] then e ~ 1;
				.. ~ 1 * e;
					apply sym;
					by left_neutral.
				by all.

			theory RightCancellative :=
				import Magmas.RightCancellative A A (*).
			begin

				lemma left_neutral_any: if ex: e * x ~ x, [e ∈ A, x ∈ A] then e ~ 1;
					apply right_cancels[of x];
					.. ~ x; by ex.
					apply sym, left_neutral.

			end

		end

		theory RightNeutral 1 :=
			import neutral: Member 1 A.
			import Magmas.RightNeutral A (*) 1.
		begin
			note! neutral.closed.
			lemma left_neutral_is_neutral:
				if all: ∀x. x ∈ A ⟹ e * x ~ x, [e ∈ A] then e ~ 1;
				.. ~ e * 1;
					apply sym;
					by right_neutral.
				by all.

			theory LeftCancellative :=
				import Magmas.LeftCancellative A A (*).
			begin

				lemma right_neutral_any: if xe: x * e ~ x, [e ∈ A, x ∈ A] then e ~ 1;
					apply left_cancels[of x];
					.. ~ x; by xe.
					apply sym, right_neutral.

			end

		end

		theory Neutral :=
			import LeftNeutral, RightNeutral.
		end

		theory LeftAbsorb 0 :=
			import absorb: Member 0 A.
			import Magmas.LeftAbsorb A (*) 0.
		begin
			note! absorb.closed.
			lemma right_absorb_is_absorb: if eq: ∀x. x ∈ A ⟹ x * z ~ z, !z ∈ A then z ~ 0;
				.. ~ 0 * z;
					apply sym;
					by eq.
				by left_absorb.
		end

		theory RightAbsorb 0 :=
			import absorb: Member 0 A.
			import Magmas.RightAbsorb A (*) 0.
		begin
			note! absorb.closed.
			lemma left_absorb_is_absorb: if eq: ∀x. x ∈ A ⟹ z * x ~ z, !z ∈ A then z ~ 0;
				.. ~ z * 0;
					apply sym;
					by eq.
				by right_absorb.
		end

		theory Absorb :=
			import LeftAbsorb, RightAbsorb.
		end

		theory LeftCancel (\) :=
			import lcancel: Magma (\).
			import lcancel: LeftMonotone A A (\).
			import Magmas.LeftCancel A A.
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

		theory RightCancel (/) :=
			import rcancel: Magma (/).
			import rcancel: RightMonotone A A (/).
			import Magmas.RightCancel A A.
		begin
			note! rcancel.closed.
			instance RightCancellative A A;
				- for y if eq: x * y ~ x' * y, ... then x ~ x';
					.. ~ x * y / y;
						apply sym;
						by right_cancel.
					.. ~ x' * y / y;
						by rcancel.right_mono eq.
					by right_cancel.
				.
		end

		extend Commutative begin

			theory Neutral :=
				import LeftNeutral.
			begin
				instance Magma.Neutral;
					- for x if [x ∈ A] then x * 1 ~ x;
						.. ~ 1 * x;
							apply commute.
						apply left_neutral.
					.
			end

			theory Absorb 0 :=
				import LeftAbsorb.
			begin
				instance Magma.Absorb;
					- for x if !x ∈ A then x * 0 ~ 0;
						.. ~ 0 * x;
							by commute.
						by left_absorb.
					.
			end

		end

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
		import Semigroup, Commutative.
	end

	theory Monoid (*) 1 :=
		import Semigroup (*), Neutral 1.
	end

	theory CommMonoid (*) 1 :=
		import CommSemigroup (*), Neutral 1.
	begin
		instance! Monoid.
	end

	theory SemigroupAbsorb (*) 0 :=
		import Semigroup (*), Absorb 0.
	end

	theory CommSemigroupAbsorb (*) 0 :=
		import CommSemigroup (*), Absorb 0.
	begin
		instance? SemigroupAbsorb.
	end

	theory MonoidAbsorb (*) 0 1 :=
		import Monoid, SemigroupAbsorb.
	end

	theory CommMonoidAbsorb (*) 0 1 :=
		import CommMonoid, CommSemigroupAbsorb.
	begin
		instance? MonoidAbsorb.
	end

	theory CommRingoid (*) (+) :=
		namespace mul begin
			import Magma (*), Commutative.
		end
		namespace add begin
			import Magma (+), Commutative, Monotone.
		end
		import LeftDistributive A A (*) (+) (+).
	begin
		note! mul.closed add.closed.
		instance Ringoid;
			- if [x ∈ A, y ∈ A, z ∈ A] then (x + y) * z ~ x * z + y * z;
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
		import Distributive.
		import mul: Semigroup (*).
		namespace add begin
			import CommSemigroup (+), Monotone.
		end
	begin
		instance Ringoid.
	end

	theory SemiringAbsorb (*) (+) 0 :=
		import Distributive.
		import mul: SemigroupAbsorb (*) 0.
		namespace add begin
			import CommMonoid (+) 0, Monotone.
		end
	begin
		instance? Semiring.
	end

	theory SemiringNeutral (*) (+) 0 1 :=
		import SemiringAbsorb.
		import mul: MonoidAbsorb (*) 0 1.
	end

	theory CommSemiring (*) (+) :=
		import LeftDistributive A A (*) (+) (+).
		import mul: CommSemigroup (*).
		namespace add begin
			import CommSemigroup (+), Monotone.
		end
	begin
		instance CommRingoid, Semiring.
	end

	theory CommSemiringAbsorb (*) (+) 0 :=
		import CommSemiring.
		import mul: CommSemigroupAbsorb (*) 0.
		import add: CommMonoid (+) 0.
	begin
		instance SemiringAbsorb.
	end

	theory CommSemiringNeutral (*) (+) 0 1 :=
		import CommSemiringAbsorb.
		import mul: CommMonoidAbsorb (*) 0 1.
	begin
		instance SemiringNeutral.
	end

	theory LeftQuasiGroup (*) (\) :=
		import Magma (*), LeftCancel (\).
		import lcancel: Magmas.LeftCancel A A (\) (*).
	end

	theory RightQuasiGroup (*) (/) :=
		import Magma (*), RightCancel (/).
		import rcancel: Magmas.RightCancel A A (/) (*).
	end

	theory QuasiGroup (*) (\) (/) :=
		import LeftQuasiGroup (*) (\).
		import RightQuasiGroup (*) (/).
	end

	theory LeftLoop (*) 1 (\) :=
		import Magma (*), Neutral 1.
		import LeftQuasiGroup (*) (\).
	end

	theory RightLoop (*) 1 (/) :=
		import Magma (*), Neutral 1.
		import RightQuasiGroup (*) (/).
	end

ctxt.
end
