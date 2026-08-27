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

theory LeftAssociative A (*) (/) :=
	assume left_assoc: if x ∈ A, y ∈ A, z ∈ A then (x * y) / z ~ x * (y / z).
end

theory RightAssociative A (*) (/) :=
	assume right_assoc: if x ∈ A, y ∈ A, z ∈ A then x * (y / z) ~ (x * y) / z.
end

theory LeftComposable A B (∘) (⋅) :=
	assume left_comp: if x ∈ A, y ∈ A, z ∈ B then (x ∘ y) ⋅ z ~ x ⋅ (y ⋅ z).
end

theory RightComposable A B (^) (*) :=
	assume right_comp: if x ∈ A, y ∈ B, z ∈ B then x ^ (y * z) ~ (x ^ y) ^ z.
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

theory LeftCancellation A B (*) (\) :=
	assume left_cancel: if x ∈ A, y ∈ B then x \ (x * y) ~ y.
end

theory RightCancellation A B (*) (/) :=
	assume right_cancel: if x ∈ A, y ∈ B then (x * y) / y ~ x.
end

theory LeftAbsorptive A B (⊓) (⊔) :=
	assume left_absorptive: if x ∈ A, y ∈ B then x ⊓ (x ⊔ y) ~ x.
end

theory RightAbsorptive A B (⊓) (⊔) :=
	assume right_absorptive: if x ∈ A, y ∈ B then (x ⊓ y) ⊔ y ~ y.
end

theory LeftInverse A (*) 1 inverse :=
	assume left_inverse: if x ∈ A then inverse x * x ~ 1.
end

theory RightInverse A (*) 1 inverse :=
	assume right_inverse: if x ∈ A then x * inverse x ~ 1.
end

theory LeftAction A B (∘) (⋅) :=
	import Magma A (∘).
	import app: Binary (⋅) A B B.
	import LeftComposable A B (∘) (⋅).
end

theory LeftModuloid A B (⋅) (+) (++) :=
	import Binary (⋅) A B B.
	import sadd: Magma A (+).
	import add: Magma B (++).
	import LeftDistributive A B (⋅) (++) (++).
	import RightDistributive A B (⋅) (+) (++).
end

theory RightModuloid A B (⋅) (+) (++) :=
	import Binary (⋅) B A B.
	import sadd: Magma A (+).
	import add: Magma B (++).
	import RightDistributive A B (⋅) (++) (++).
	import LeftDistributive A B (⋅) (+) (++).
end

theory Ringoid A (*) (+) :=
	import Magma A (*).
	import add: Magma A (+).
	import Distributive A (*) (+).
begin

	instance LeftModuloid A A (*) (+) (+); by closed add.closed.

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
					.. ⊏ x' * y; apply right_mono[OF x].
					apply left_mono[OF y].
				.
		end

	end

	theory CommMagma :=
		import Magma, Commutative.
	begin

		theory Monotone :=
			import LeftMonotone A A.
		begin
			instance Magma.Monotone;
				- if xx': x ⊏ x', ... for y if ... then x * y ⊏ x' * y;
					.. ⊏ y * x; apply commute.
					.. ⊏ y * x'; apply left_mono[OF xx'].
					apply commute.
				.
		end

	end

end

context PartialEquivalence begin

	instance Magmas (~).

	extend Transitive.Magma begin

		theory LeftCancel (\) :=
			import lcancel: Magma (\).
			import lcancel: LeftMonotone A A (\).
			import Magmas.LeftCancellation A A (*) (\).
		begin
			note! lcancel.closed.
			instance LeftCancellative A A;
				- if eq: x * y ~ x * y', ... then y ~ y';
					.. ~ x \ (x * y); apply sym, left_cancel.
					.. ~ x \ (x * y'); apply lcancel.left_mono, eq.
					apply left_cancel.
				.
		end

		theory RightCancel (/) :=
			import cancel: Magma (/).
			import cancel: RightMonotone A A (/).
			import Magmas.RightCancellation A A (*) (/).
		begin
			note! cancel.closed.
			instance RightCancellative A A;
				- for y if eq: x * y ~ x' * y, ... then x ~ x';
					.. ~ x * y / y; apply sym, right_cancel.
					.. ~ x' * y / y; apply cancel.right_mono, eq.
					apply right_cancel.
				.
		end

		theory LeftNeutral 1 :=
			import neutral: Member 1 A.
			import Magmas.LeftNeutral A (*) 1.
			import RightMonotone A A (*).
		begin
			note! neutral.closed.

			lemma left_neutral_intro: if e: e ~ 1, [e ∈ A, x ∈ A] then e * x ~ x;
				.. ~ 1 * x; apply right_mono, e.
				apply left_neutral.

			lemma right_neutral_is_neutral:
				if all: ∀x. x ∈ A ⟹ x * e ~ x, [e ∈ A] then e ~ 1;
				.. ~ 1 * e; apply sym, left_neutral.
				apply all.

			theory RightCancellative :=
				import Magmas.RightCancellative A A (*).
			begin

				lemma left_neutral_any: for x if ex: e * x ~ x, [e ∈ A, x ∈ A] then e ~ 1;
					apply right_cancels[of x];
					.. ~ x; apply ex.
					apply sym, left_neutral.

			end

			extend RightCancel begin
				instance RightCancellative.
			end

		end

		theory RightNeutral 1 :=
			import neutral: Member 1 A.
			import Magmas.RightNeutral A (*) 1.
			import LeftMonotone A A (*).
		begin
			note! neutral.closed.

			lemma right_neutral_intro: if e: e ~ 1, [x ∈ A, e ∈ A] then x * e ~ x;
				.. ~ x * 1; apply left_mono, e.
				apply right_neutral.

			lemma left_neutral_is_neutral:
				if all: ∀x. x ∈ A ⟹ e * x ~ x, [e ∈ A] then e ~ 1;
				.. ~ e * 1; apply sym, right_neutral.
				apply all.

			theory LeftCancellative :=
				import Magmas.LeftCancellative A A (*).
			begin

				lemma right_neutral_any: for x if xe: x * e ~ x, [e ∈ A, x ∈ A] then e ~ 1;
					apply left_cancels[of x];
					.. ~ x; apply xe.
					apply sym, right_neutral.

			end

			extend LeftCancel begin
				instance LeftCancellative.
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
				.. ~ 0 * z; apply eq[dual].
				apply left_absorb.
		end

		theory RightAbsorb 0 :=
			import absorb: Member 0 A.
			import Magmas.RightAbsorb A (*) 0.
		begin
			note! absorb.closed.
			lemma left_absorb_is_absorb: if eq: ∀x. x ∈ A ⟹ z * x ~ z, !z ∈ A then z ~ 0;
				.. ~ z * 0; apply eq[dual].
				apply right_absorb.
		end

		theory Absorb :=
			import LeftAbsorb, RightAbsorb.
		end

	end

	extend CommMagma begin

		instance? Magma.

		theory Neutral :=
			import Monotone, LeftNeutral.
		begin
			instance Magma.Neutral;
				- for x if [x ∈ A] then x * 1 ~ x;
					.. ~ 1 * x; apply commute.
					apply left_neutral.
				.
		end

		theory Absorb 0 :=
			import LeftAbsorb 0.
		begin
			instance Magma.Absorb 0;
				- for x if !x ∈ A then x * 0 ~ 0;
					.. ~ 0 * x; apply commute.
					apply left_absorb.
				.
		end

	end

	theory Semigroup :=
		import Magma, LeftAssociative A (*) (*).
	begin
		instance RightAssociative A (*) (*);
			- if ! x ∈ A, ! y ∈ A, ! z ∈ A;
				apply sym, left_assoc.
			.

	end

	theory CommSemigroup :=
		import Semigroup, CommMagma.-- Notions defined in CommMagma should take precedence.
	begin
	end

	theory Monoid (*) 1 :=
		import Semigroup (*), Neutral 1.
	end

	theory CommMonoid (*) 1 :=
		import CommSemigroup (*), Neutral 1.
	begin
		instance? Monoid.
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
		import CommMagma (*).
		import add: CommMagma (+), add.Monotone.
		import LeftDistributive A A (*) (+) (+).
	begin
		note! closed add.closed.
		instance Ringoid;
			- if [x ∈ A, y ∈ A, z ∈ A] then (x + y) * z ~ x * z + y * z;
				.. ~ z * (x + y); apply commute.
				.. ~ z * x + z * y; apply left_distrib.
				apply add.comp;
				- apply commute.
				- apply commute.
				.
			.
	end

	theory Semiring (*) (+) :=
		import Semigroup (*).
		import add: CommSemigroup (+), add.Monotone.
		import Distributive.
	begin
		instance Ringoid.
	end

	theory Semiring0 (*) (+) 0 :=
		import Semiring (*) (+).
		import SemigroupAbsorb (*) 0.
		import add: Magmas.LeftNeutral A (+) 0.
	begin
		instance add: CommMonoid (+) 0.
	end

	theory Semiring1 (*) (+) 0 1 :=
		import Semiring0 (*) (+) 0.
		import MonoidAbsorb (*) 0 1.
	begin
	end

	theory CommSemiring (*) (+) :=
		import CommSemigroup (*).
		import add: CommSemigroup (+), add.Monotone.
		import LeftDistributive A A (*) (+) (+).
	begin
		instance CommRingoid, Semiring.
	end

	theory CommSemiring0 (*) (+) 0 :=
		import CommSemigroupAbsorb (*) 0.
		import add: CommMonoid (+) 0;
			show: 0 ∈ A.
			.
		import LeftDistributive A A (*) (+) (+).
	begin
		instance CommSemiring (*) (+), Semiring0.
	end

	theory CommSemiring1 (*) (+) 0 1 :=
		import CommMonoidAbsorb (*) 0 1.
		import CommSemiring0 (*) (+) 0.
	begin
		instance Semiring1.
	end

	theory BooleanAlgebra (&) (|) 0 1 :=
		import CommMonoidAbsorb (&) 0 1, Idempotent A (&).
		import dual: CommMonoidAbsorb (|) 1 0, Idempotent A (|).
		import LeftDistributive A A (&) (|) (|), LeftAbsorptive A A (&) (|).
		import dual: LeftDistributive A A (|) (&) (&), LeftAbsorptive A A (|) (&).
	begin

		instance CommSemiring1 (&) (|) 0 1;
			by closed left_assoc left_mono left_neutral left_absorb commute
			   neutral.closed absorb.closed
			   dual.closed dual.left_assoc dual.commute dual.left_mono dual.left_neutral.

		instance dual: CommSemiring1 (|) (&) 1 0;
			by dual.closed dual.left_assoc dual.commute dual.left_mono dual.left_neutral
			   neutral.closed absorb.closed dual.left_absorb
				left_assoc commute left_mono left_neutral.

	end

	theory LeftQuasiGroup (*) (\) :=
		import Magma (*), LeftCancel (\).
		import lcancel: Magmas.LeftCancellation A A (\) (*).
	end

	theory RightQuasiGroup (*) (/) :=
		import Magma (*), RightCancel (/).
		import cancel: Magmas.RightCancellation A A (/) (*).
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

	theory GroupInverse (*) 1 inverse :=
		import Semigroup (*), Monotone, LeftNeutral 1.
		import inverse: Unary inverse A A.
		import LeftInverse A (*) 1 inverse.
		assume inverse_mono: if x ~ x', x ∈ A, x' ∈ A then inverse x ~ inverse x'.
	begin

		note! inverse.closed.

		lemma inverse_left_cancels: if [x ∈ A, y ∈ A] then inverse x * (x * y) ~ y;
			.. ~ inverse x * x * y; apply right_assoc.
			.. ~ 1 * y; apply right_mono left_inverse.
			apply left_neutral.

		instance Monoid;
			- if [x ∈ A] then x * 1 ~ x;
				.. ~ inverse (inverse x) * (inverse x * (x * 1)); apply inverse_left_cancels[dual].
				.. ~ inverse (inverse x) * 1; apply left_mono inverse_left_cancels.
				.. ~ inverse (inverse x) * (inverse x * x); apply left_mono left_inverse[dual].
				apply inverse_left_cancels.
			.

		lemma inverse_neutral: inverse 1 ~ 1;
			.. ~ inverse 1 * 1; apply right_neutral[dual].
			apply left_inverse.

		lemma inverse_inverse: if [x ∈ A] then inverse (inverse x) ~ x;			
			.. ~ inverse (inverse x) * 1; apply right_neutral[dual].
			.. ~ inverse (inverse x) * (inverse x * x); apply left_mono, left_inverse[dual].
			apply inverse_left_cancels.

		instance RightInverse A (*) 1 inverse;
			- if [x ∈ A] then x * inverse x ~ 1;
				.. ~ inverse (inverse x) * inverse x; apply right_mono, inverse_inverse[dual].
				apply left_inverse.
			.

		lemma cancels_inverse_left: if [x ∈ A, y ∈ A] then x * (inverse x * y) ~ y;
			.. ~ inverse (inverse x) * (inverse x * y); apply right_mono, inverse_inverse[dual].
			apply inverse_left_cancels.

		lemma inverse_compose: if [x ∈ A, y ∈ A] then inverse (x * y) ~ inverse y * inverse x;
			.. ~ inverse y * (y * inverse (x * y)); apply inverse_left_cancels[dual].
			apply left_mono;
			.. ~ inverse x * (x * (y * inverse (x * y))); apply inverse_left_cancels[dual].
			apply right_neutral_intro;
			.. ~ (x * y) * inverse (x * y); apply right_assoc.
			apply right_inverse.

		lemma inverse_right_cancels: if [x ∈ A, y ∈ A] then x * y * inverse y ~ x;
			.. ~ x * (y * inverse y); apply left_assoc.
			.. ~ x * 1; apply left_mono, right_inverse.
			apply right_neutral.

		instance LeftCancellative;
			- if eq: x * y ~ x * y', ... then y ~ y';
				.. ~ inverse x * (x * y); apply inverse_left_cancels[dual].
				.. ~ inverse x * (x * y'); apply left_mono, eq.
				apply inverse_left_cancels.
			.

		instance RightCancellative;
			- for y if eq: x * y ~ x' * y, ... then x ~ x';
				.. ~ x * y * inverse y; apply inverse_right_cancels[dual].
				.. ~ x' * y * inverse y; apply right_mono, eq.
				apply inverse_right_cancels.
			.

	end

	theory GroupCancel (*) 1 (/) :=
		import Semigroup (*), Monotone, LeftNeutral 1, RightQuasiGroup (*) (/).
		import cancel: LeftMonotone A A (/), RightAssociative A (*) (/).
	begin

		lemma cancel_self: if [x ∈ A] then x / x ~ 1;
			.. ~ 1 * x / x; apply cancel.right_mono, left_neutral[dual].
			apply right_cancel.

		instance GroupInverse (*) 1 (1 /);
			- if [x ∈ A] then 1 / x ∈ A.
			- if [x ∈ A] then (1 / x) * x ~ 1; apply cancel.right_cancel.
			- if [x ~ x', x ∈ A, x' ∈ A] then 1 / x ~ 1 / x'; apply cancel.left_mono.
			.

		lemma cancel_neutral: if [x ∈ A] then x / 1 ~ x;
			.. ~ x * 1 / 1; apply cancel.right_mono, right_neutral[dual].
			apply right_cancel.

		lemma inverse_to_cancel: if [x ∈ A, y ∈ A] then x * (1 / y) ~ x / y;
			.. ~ x * 1 / y; apply cancel.right_assoc.
			apply cancel.right_mono, right_neutral.

		instance cancel: LeftAssociative A (*) (/);
			- if [x ∈ A, y ∈ A, z ∈ A] then x * y / z ~ x * (y / z);
				apply cancel.right_assoc[dual].
			.

		lemma cancel_cancel:
			if [x ∈ A, y ∈ A, z ∈ A] then x / y / z ~ x / (z * y);
			.. ~ (x/y) * (1/z); apply inverse_to_cancel[dual].
			.. ~ x * (1/y) * (1/z); apply right_mono, inverse_to_cancel[dual].
			.. ~ x * ((1/y) * (1/z)); apply left_assoc.
			.. ~ x * (1 / (z * y)); apply left_mono, inverse_compose[dual].
			.. ~ x * 1 / (z * y); apply cancel.right_assoc.
			apply cancel.right_mono, right_neutral.

	end

	theory CommGroupCancel (*) 1 (/) :=
		import CommMonoid (*) 1, Monotone.
		import RightCancel (/).
		import cancel:
			Magmas.RightCancellation A A (/) (*),
			LeftMonotone A A (/),
			RightAssociative A (*) (/).
	begin

		instance GroupCancel.

	end

end

context Equivalence begin

	instance PartialEquivalence.

end
