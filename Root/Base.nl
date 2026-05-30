------
# Base
------

begin -- Base doesn't have any axiom

---
## Notations
---

set symbol
	¬,
	Γ-Δ, Θ, Λ, Ξ, Π, Σ, Φ, Ψ-Ω, α-ξ, π-ω,-- Greek
	ℂ, ℋ, ℍ, ℐ-ℓ, ℕ, ℘-ℝ, ℤ, ℬ-ℭ, ℰ-ℱ, ℵ-ℸ, ℼ-⅀, ⅅ-ⅉ, -- Letterlike Symbols
	𝒜, 𝒞-𝒟, 𝒢, 𝒥-𝒦, 𝒩-𝒬, 𝒮-𝒵, 𝔸-𝔹, 𝔻-𝔾, 𝕀-𝕄, 𝕆, 𝕊-𝕐,𝕒-𝕫, 𝟘-𝟡, -- Mathematical Alphanumeric Symbols
	∀-⋿, -- Mathematical Operators
	⟀-⟯, -- Miscellaneous Mathematical Symbols-A
	←-⇿, -- Arrows
	⟰-⟿, -- Supplemental Arrows-A
	⨀-⫿. -- Supplemental Mathematical Operators

infix ⟹ 1 0 0.
binder ∀ 0 0.

infix ⟺ 1 1 0.
infix ∨ 10 11 10.
infix ∧ 20 21 20.
prefix ¬ 30 30.
binder ∃ 0 0.
binder ∃! 0 0.
binder fun 51 0.
binder FUN 51 0.
binder such 51 0.

infix ∈ 51 51 50.
syntax ∀ _ ∈ _. _ := ∀∈.
syntax ∃ _ ∈ _. _ := ∃∈.
syntax ∃! _ ∈ _. _ := ∃!∈.
syntax fun _ ∈ _. _ := fun.∈.
syntax FUN _ ∈ _. _ := FUN.∈.
syntax such _ ∈ _. _ := such.∈.
syntax {_ ∈ _. _} := Collect.∈.

infix ⊆ 51 51 50.

infix = 51 51 50.
infix ≡ 51 51 50.
infix ≠ 51 51 50.
infix ~ 51 51 50.
infix ∋ 51 51 50.
infix ∉ 51 51 50.
infix ⊂ 51 51 50.
infix ⊇ 51 51 50.
infix ⊃ 51 51 50.

infix < 51 51 50.
syntax ∀ _ < _. _ := ∀<.
syntax ∃ _ < _. _ := ∃<.
syntax ∃! _ < _. _ := ∃!<.
syntax such _ < _. _ := such.<.
syntax {_ < _. _} := Collect.<.

infix ≤ 51 51 50.
infix > 51 51 50.
infix ≥ 51 51 50.
infix ⊑ 51 51 50.
infix ⊒ 51 51 50.
infix ⊏ 51 51 50.
syntax ∀ _ ⊏ _. _ := ∀⊏.
syntax ∃ _ ⊏ _. _ := ∃⊏.
syntax ∃! _ ⊏ _. _ := ∃!⊏.
syntax such _ ⊏ _. _ := such.⊏.
syntax {_ ⊏ _. _} := Collect.⊏.

infix ⊐ 51 51 50.

infix |> 60 61 60.-- reverse application

infix → 61 60 60.

infix + 100 101 100.
infix - 100 101 100.
infix ⋅ 191 190 190.
infix * 200 201 200.
infix / 200 201 200.
infix \ 201 200 200.
infix ^ 300 301 300.

---
## Type-Free Binary Relations
---
theory MetaRelation:
	fix (⊏).
begin

	theory AllRel:
		fix (∀⊏).
		assume all_intro! if ∀x. x ⊏ a ⟹ P.[x] then ∀x ⊏ a. P.[x].
		assume all_elim1: for x if ∀y ⊏ a. P.[y], x ⊏ a then P.[x].
	begin
		lemma all_elim: if all: ∀x ⊏ a. P.[x], imp: (∀x. x ⊏ a ⟹ P.[x]) ⟹ Q then Q;
			by imp all_elim1[OF all].
	end

	theory MetaCompatible:
		fix (*).
		assume cong: if x ⊏ x', y ⊏ y' then x * y ⊏ x' * y'.
	end

	theory MetaLeftMonotone:
		fix (*).
		assume left_mono: if y ⊏ y' then x * y ⊏ x * y'.
	end

	theory MetaRightMonotone:
		fix (*).
		assume right_mono: if x ⊏ x' then x * y ⊏ x' * y.
	end

	theory MetaMonotone:
		import MetaLeftMonotone.
		import MetaRightMonotone.
	end

	theory MetaCommutative:
		fix (*).
		assume commute: x * y ⊏ y * x.
	end

	theory MetaLeftAssociative:
		fix (*) (⋅).
		assume left_assoc: x * y ⋅ z ⊏ x ⋅ y ⋅ z.
	end

	theory MetaRightAssociative:
		fix (^) (*).
		assume right_assoc: x ^ (y * z) ⊏ x ^ y ^ z.
	end

	theory MetaIdempotent:
		fix (*).
		assume idem: x * x ⊏ x.
	end

	theory MetaLeftNeutral:
		fix (*) (1).
		assume left_neutral: 1 * x ⊏ x.
	end

	theory MetaRightNeutral:
		fix (*) (1).
		assume right_neutral: x * 1 ⊏ x.
	end

	theory MetaNeutral:
		import MetaLeftNeutral.
		import MetaRightNeutral.
	end

	theory MetaLeftAbsorb:
		fix (*) (0).
		assume left_absorb: 0 * x ⊏ 0.
	end

	theory MetaRightAbsorb:
		fix (*) (0).
		assume right_absorb: x * 0 ⊏ 0.
	end

	theory MetaAbsorb:
		import MetaLeftAbsorb.
		import MetaRightAbsorb.
	end

end

theory MetaReflexive:
	fix (⊏).
	assume refl: x ⊏ x.
begin
	interpret? MetaRelation.
	extend MetaCompatible begin
		interpret MetaMonotone;
			by cong refl.
	end
end

theory MetaTransitive:
	fix (⊏).
	assume trans: if x ⊏ y, y ⊏ z then x ⊏ z.
begin
	interpret? MetaRelation.
	extend MetaMonotone begin
		interpret MetaCompatible;
			- if xx': x ⊏ x', yy': y ⊏ y' then x * y ⊏ x' * y';
				have 1: x * y ⊏ x' * y;
					by right_mono xx'.
				apply trans[OF 1];
				by left_mono yy'.
			.
	end

end

theory MetaPreorder:
	import MetaReflexive.
	import MetaTransitive.
end

theory MetaSymmetric:
	fix (⊏).
	assume sym: if x ⊏ y then y ⊏ x.
end

theory MetaTolerance:
	import MetaReflexive.
	import MetaSymmetric.
end

theory MetaPartialEquivalence:
	import MetaSymmetric.
	import MetaTransitive.
begin

	interpret? MetaRelation.

	theory MetaSemigroup:
		fix (*).
		import MetaLeftAssociative (*) (*).
	begin
		interpret MetaRightAssociative (*) (*);
			- for x y z;
				apply sym;
				by left_assoc.
			.
	end

	theory MetaCommSemigroup:
		import MetaSemigroup.
		import MetaCommutative.
	end

	extend MetaLeftNeutral begin
		interpret MetaReflexive;
			- for x then x ⊏ x;
				have 1: x ⊏ 1 * x;
					apply sym;
					by left_neutral.
				apply trans[OF 1];
				by left_neutral.
			.
		lemma right_neutral_is_neutral: if all: ∀x. x * e ⊏ x then e ⊏ 1;
			have 1: e ⊏ 1 * e;
				apply sym;
				by left_neutral.
			apply trans[OF 1];
			by all.
	end

	extend MetaRightNeutral begin
		interpret MetaReflexive (⊏);
			- for x then x ⊏ x;
				have 1: x ⊏ x * 1;
					apply sym;
					by right_neutral.
				apply trans[OF 1];
				by right_neutral.
			.
		lemma left_neutral_is_neutral: if all: ∀x. e * x ⊏ x then e ⊏ 1;
			have 1: e ⊏ e * 1;
				apply sym;
				by right_neutral.
			apply trans[OF 1];
			by all.
	end

	extend MetaNeutral begin
		interpret MetaLeftNeutral.
		interpret MetaRightNeutral.
	end

	theory MetaCommNeutral:
		import MetaLeftNeutral.
		import MetaCommutative.
	begin
		interpret MetaNeutral;
			by trans[OF commute left_neutral].
	end

	theory MetaMonoid:
		import MetaNeutral.
		import MetaSemigroup.
	end

	theory MetaCommMonoid:
		import MetaCommNeutral.
		import MetaCommSemigroup.
	begin
		interpret MetaMonoid.
	end

	extend MetaLeftAbsorb begin
		lemma right_absorb_is_absorb: if all: ∀x. x * e ⊏ e then e ⊏ 0;
			have 1: e ⊏ 0 * e;
				apply sym;
				by all.
			apply trans[OF 1];
			by left_absorb.
	end

	extend MetaRightAbsorb begin
		lemma left_absorb_is_absorb: if all: ∀x. e * x ⊏ e then e ⊏ 0;
			have 1: e ⊏ e * 0;
				apply sym;
				by all.
			apply trans[OF 1];
			by right_absorb.
	end

	extend MetaAbsorb begin
		interpret MetaLeftAbsorb.
		interpret MetaRightAbsorb.
	end

	theory MetaCommAbsorb:
		import MetaLeftAbsorb.
		import MetaCommutative.
	begin
		interpret MetaAbsorb;
			by trans[OF commute left_absorb].
	end

	theory MetaSemigroupAbsorb:
		import MetaAbsorb.
		import MetaSemigroup.
	end

	theory MetaCommSemigroupAbsorb:
		import MetaCommAbsorb.
		import MetaCommSemigroup.
	begin
		interpret MetaSemigroupAbsorb.
	end

	theory MetaMonoidAbsorb:
		fix (*) 0 1.
		import MetaAbsorb.
		import MetaMonoid.
	begin
		interpret MetaSemigroupAbsorb.
	end

	theory MetaCommMonoidAbsorb:
		fix (*) 0 1.
		import MetaCommAbsorb.
		import MetaCommMonoid.
	begin
		interpret MetaMonoidAbsorb.
		interpret MetaCommSemigroupAbsorb.
	end

end

theory MetaEquivalence:
	import MetaReflexive.
	import MetaSymmetric.
	import MetaTransitive.
begin
	interpret MetaTolerance.
	interpret MetaPreorder.
	interpret MetaPartialEquivalence.
ctxt.
end

---
## Theorems in Foundation
---

-- Implication is a meta-preorder.
interpret imp: MetaPreorder (⟹);
	- if PQ: P ⟹ Q, QR: Q ⟹ R then P ⟹ R;
		by QR PQ.
	.

lemma mp: if P: P, PQ: P ⟹ Q then Q;
	by PQ[OF P].

lemma weaken: if P: P, Q: Q then P;
	by P.

lemma ignore: if PQR: (P ⟹ Q) ⟹ R, Q: Q then R;
	by PQR Q.

lemma imp_commute: if PQR: P ⟹ Q ⟹ R then Q ⟹ P ⟹ R;
	by PQR.

lemma insert: if PQ: P ⟹ Q, RP: R ⟹ P then R ⟹ Q;
	by PQ RP.

lemma imp2_imp_imp: if PQQR: ((P ⟹ Q) ⟹ Q) ⟹ R, P! P then R;
	apply PQQR;
	- if PQ: P ⟹ Q then Q;
		by PQ.
	.

lemma imp_all: if imp: P ⟹ ∀x. Q.[x] then ∀x. P ⟹ Q.[x];
	by imp.

lemma all_indep_imp: if all: ∀x. P ⟹ Q.[x] then P ⟹ ∀x. Q.[x];
	by all.

lemma all_all_imp: if all: ∀x. P.[x], imp: ∀x. P.[x] ⟹ Q.[x] then ∀x. Q.[x];
	by imp all.
