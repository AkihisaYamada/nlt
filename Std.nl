------
# Standard Library
------
begin
---
## Notations
---
set symbol
	¬,
	Γ-Δ, Θ, Λ, Ξ, Π, Σ, Φ, Ψ-Ω, α-ξ, π-ω,-- Greek
	ℂ, ℋ, ℍ, ℐ-ℓ, ℕ, ℘-ℝ, ℤ, ℬ-ℭ, ℰ-ℱ, ℵ-ℸ, ℼ-⅀, ⅅ-ⅉ, -- Letterlike Symbols
	𝒜, 𝒞-𝒟, 𝒢, 𝒥-𝒦, 𝒩-𝒬, 𝒮-𝒵, 𝔸-𝔹, 𝔻-𝔾, 𝕀-𝕄, 𝕆, 𝕊-𝕐,𝕒-𝕫, 𝟘-𝟡, -- Mathematical Alphanumeric Symbols
	∀-⋿, -- Mathematical Operators
	⁻, ¹, ², -- Some superscripts
	←-⇿, -- Arrows
	⟰-⟿, -- Supplemental Arrows-A
	⨀-⫿. -- Supplemental Mathematical Operators

set left ⟦, ⟨, ⟪.
set right ⟧, ⟩, ⟫.

infix ⟹ 1 0 0.
binder ∀ 0 0.
syntax[invalid] _ }.
syntax[invalid] _ ].

infix ⟸ 0 1 0.
infix ⟺ 1 1 0.
infix ⟶ 11 10 10.
infix ⟷ 11 11 10.
infix ∨ 20 21 20.
infix || 20 21 20.
infix ∧ 30 31 30.
infix && 30 31 30.
prefix ¬ 40 40.
binder ∃ 0 0.
binder ∃! 0 0.
binder fun 51 -10.
binder FUN 51 -10.
binder some 50 -10.
binder the 50 -10.
binder such 50 -10.

syntax { _ } := {_}.
syntax ∀ _ : _. _ := ∀:.
syntax ∃ _ : _. _ := ∃:.
syntax ∃! _ : _. _ := ∃!:.
syntax fun _ : _. _ := fun_:.
syntax FUN _ : _. _ := FUN_:.
syntax the _ : _. _ := the_:.
syntax some _ : _. _ := some_:.
syntax such _ : _. _ := such_:.
syntax { _ : _. _ } := {_:_}.

infix ∈ 51 51 50.
syntax ∀ _ ∈ _. _ := ∀∈.
syntax ∃ _ ∈ _. _ := ∃∈.
syntax ∃! _ ∈ _. _ := ∃!∈.
syntax fun _ ∈ _. _ := fun_∈.
syntax FUN _ ∈ _. _ := FUN_∈.
syntax the _ ∈ _. _ := the_∈.
syntax some _ ∈ _. _ := some_∈.
syntax { _ ∈ _. _ } := {_∈_}.

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
infix ≤ 51 51 50.
infix > 51 51 50.
infix ≥ 51 51 50.
infix ⊑ 51 51 50.
infix ⊒ 51 51 50.
infix ⊏ 51 51 50.
syntax ∀ _ ⊏ _. _ := ∀⊏.
syntax ∃ _ ⊏ _. _ := ∃⊏.
syntax ∃! _ ⊏ _. _ := ∃!⊏.
syntax { _ ⊏ _. _ } := {_⊏_}.

infix ⊐ 51 51 50.

infix |> 60 61 60.-- reverse application

infix → 61 60 60.
infix ⇒ 61 60 60.

infix ∪ 70 71 70.
infix ⊔ 70 71 70.
infix | 70 71 70.
infix ∩ 80 81 80.
infix ⊓ 80 81 80.
infix & 80 81 80.
infix × 201 200 200.

infix + 100 101 100.
infix - 100 101 100 := _-_.
infix ⋅ 191 190 190.
infix * 200 201 200.
infix / 200 201 200.
infix \ 201 200 200.
prefix - 301 300 := -_.
infix ^ 400 401 400.
infix ++ 100 101 100.
infix ** 200 201 200.
infix ∘ 900 901 900.

syntax[level 1000] _ ⁻ .
syntax[level 1000] _ ⁻¹ .

---
## Theories

### Type-Free Binary Relations
---
theory MetaRelation (⊏) :=
begin

	theory MetaCompatible (*) :=
		assume cong: if x ⊏ x', y ⊏ y' then x * y ⊏ x' * y'.
	end

	theory MetaLeftMonotone (*) :=
		assume left_mono: for x if y ⊏ y' then x * y ⊏ x * y'.
	end

	theory MetaRightMonotone (*) :=
		assume right_mono: for y if x ⊏ x' then x * y ⊏ x' * y.
	end

	theory MetaMonotone :=
		import MetaLeftMonotone, MetaRightMonotone.
	end

	theory MetaCommutative (*) :=
		assume commute: x * y ⊏ y * x.
	end

	theory MetaLeftAssociative (*) (⋅) :=
		assume left_assoc: x * y ⋅ z ⊏ x ⋅ y ⋅ z.
	end

	theory MetaRightAssociative (^) (*) :=
		assume right_assoc: x ^ (y * z) ⊏ x ^ y ^ z.
	end

	theory MetaIdempotent (*) :=
		assume idem: x * x ⊏ x.
	end

	theory MetaLeftNeutral (*) (1) :=
		assume left_neutral: 1 * x ⊏ x.
	end

	theory MetaRightNeutral (*) (1) :=
		assume right_neutral: x * 1 ⊏ x.
	end

	theory MetaNeutral :=
		import MetaLeftNeutral, MetaRightNeutral.
	end

	theory MetaLeftAbsorb (*) (0) :=
		assume left_absorb: 0 * x ⊏ 0.
	end

	theory MetaRightAbsorb (*) (0) :=
		assume right_absorb: x * 0 ⊏ 0.
	end

	theory MetaAbsorb :=
		import MetaLeftAbsorb, MetaRightAbsorb.
	end

end

theory MetaReflexive (⊑) :=
	assume refl: x ⊑ x.
begin
	instance? MetaRelation (⊑).
	extend MetaCompatible begin
		instance MetaMonotone; by cong refl.
	end
end

theory MetaTransitive (⊏) :=
	assume trans#trans if x ⊏ y, y ⊏ z then x ⊏ z.
begin
	instance? MetaRelation.
	extend MetaMonotone begin
		instance MetaCompatible;
			- if xx': x ⊏ x', yy': y ⊏ y' then x * y ⊏ x' * y';
				.. ⊏ x' * y; by right_mono xx'.
				by left_mono yy'.
			.
	end

end

theory MetaPreorder (⊑) :=
	import MetaReflexive (⊑), MetaTransitive (⊑).
end

theory MetaSymmetric (~) :=
	assume sym: if x ~ y then y ~ x.
end

theory MetaPartialEquivalence (~) :=
	import MetaSymmetric (~), MetaTransitive (~).
begin

	instance? MetaRelation (~).

	theory MetaSemigroup (*) :=
		import MetaLeftAssociative (*) (*).
	begin
		instance MetaRightAssociative (*) (*);
			- for x y z;
				apply sym;
				by left_assoc.
			.
	end

	theory MetaCommSemigroup :=
		import MetaSemigroup, MetaCommutative.
	end

	extend MetaLeftNeutral begin
		instance MetaReflexive (~);
			- for x then x ~ x;
				.. ~ 1 * x; apply sym, left_neutral.
				apply left_neutral.
			.
		lemma right_neutral_is_neutral: if all: ∀x. x * e ~ x then e ~ 1;
			.. ~ 1 * e; apply sym, left_neutral.
			apply all.
	end

	extend MetaRightNeutral begin
		instance MetaReflexive (~);
			- for x then x ~ x;
				.. ~ x * 1; apply sym, right_neutral.
				apply right_neutral.
			.
		lemma left_neutral_is_neutral: if all: ∀x. e * x ~ x then e ~ 1;
			.. ~ e * 1; apply sym, right_neutral.
			apply all.
	end

	extend MetaNeutral begin
		instance MetaLeftNeutral, MetaRightNeutral.
	end

	theory MetaCommNeutral :=
		import MetaLeftNeutral, MetaCommutative.
	begin
		instance MetaNeutral;
			by trans[OF commute left_neutral].
	end

	theory MetaMonoid :=
		import MetaNeutral, MetaSemigroup.
	end

	theory MetaCommMonoid :=
		import MetaCommNeutral, MetaCommSemigroup.
	begin
		instance MetaMonoid.
	end

	extend MetaLeftAbsorb begin
		lemma right_absorb_is_absorb: if all: ∀x. x * e ~ e then e ~ 0;
			.. ~ 0 * e; apply sym, all.
			apply left_absorb.
	end

	extend MetaRightAbsorb begin
		lemma left_absorb_is_absorb: if all: ∀x. e * x ~ e then e ~ 0;
			.. ~ e * 0; apply sym, all.
			apply right_absorb.
	end

	extend MetaAbsorb begin
		instance MetaLeftAbsorb, MetaRightAbsorb.
	end

	theory MetaCommAbsorb :=
		import MetaLeftAbsorb, MetaCommutative.
	begin
		instance MetaAbsorb;
			by trans[OF commute left_absorb].
	end

	theory MetaSemigroupAbsorb :=
		import MetaAbsorb, MetaSemigroup.
	end

	theory MetaCommSemigroupAbsorb :=
		import MetaCommAbsorb, MetaCommSemigroup.
	begin
		instance MetaSemigroupAbsorb.
	end

	theory MetaMonoidAbsorb (*) 0 1 :=
		import MetaAbsorb, MetaMonoid.
	begin
		instance MetaSemigroupAbsorb.
	end

	theory MetaCommMonoidAbsorb (*) 0 1 :=
		import MetaCommAbsorb, MetaCommMonoid.
	begin
		instance MetaMonoidAbsorb, MetaCommSemigroupAbsorb.
	end

end

theory MetaEquivalence (~) :=
	import MetaReflexive (~), MetaSymmetric (~), MetaPreorder (~).
begin
	instance MetaPartialEquivalence.
end

theory MetaLeftBound (⊏) ⊥ :=
	assume left_bound: ⊥ ⊏ x.
end

theory MetaRightBound (⊏) ⊤ :=
	assume right_bound: x ⊏ ⊤.
end

theory MetaMonotone f (<) (⊏) :=
	assume mono: if x < y then f x ⊏ f y.
end

theory MetaAntitone f (<) (⊏) :=
	assume cmono: if x < y then f y ⊏ f x.
end

theory MetaInvMonotone f (<) (⊏) :=
	assume inv_mono: if f x ⊏ f y then x < y.
end

theory MetaInvAntitone f (<) (⊏) :=
	assume inv_cmono: if f x ⊏ f y then y < x.
end

theory AllRel (⊏) :=
	fix (∀⊏).
	assume all_intro#intro if ∀x. x ⊏ a ⟹ P.[x] then ∀x ⊏ a. P.[x].
	assume all_elim1: for x if ∀y ⊏ a. P.[y], x ⊏ a then P.[x].
begin

	lemma all_elim#elim if all: ∀x ⊏ a. P.[x], imp: (∀x. x ⊏ a ⟹ P.[x]) ⟹ Q then Q;
		by imp all_elim1[OF all].

end

theory ExRel (⊏) :=
	fix (∃⊏).
	assume ex_intro1: for x if P.[x], x ⊏ a then ∃x ⊏ a. P.[x].
	assume ex_elim: if ∃x ⊏ a. P.[x], ∀x. P.[x] ⟹ x ⊏ a ⟹ Q then Q.
begin

	lemma ex_intro: if assm: ∀Q. (∀x. P.[x] ⟹ x ⊏ a ⟹ Q) ⟹ Q then ∃x ⊏ a. P.[x];
		apply assm;
		- if Px: P.[x], xa: x ⊏ a; by ex_intro1[OF Px xa].
		.

end

---
### Tiny Logical Theories

It is safe to declare true and false, but it is also natural to put more assumptions later,
e.g. `true ∈ Prop`. So here we encapsulate them in theories with no assumptions.
---
theory True begin

	obtain true where true_intro! true;
		- for thesis if assm; by assm[of (∀P. P ⟹ P)].
		.
	instance imp: MetaRightBound (⟹) true.

end

theory False begin

	obtain false where false_elim#elim
		-- @English Law of Explosion
		-- @Latin ex falso quodlibet
		if false then P;
		- for thesis if assm; by assm[of (∀P. P)].
		.

	instance imp: MetaLeftBound (⟹) false.

end

-- @English Peirce's law
-- The following version does not restrict to propositions.
theory PeirceLaw :=
	assume peirce_law: for Q if (P ⟹ Q) ⟹ P then P.
end

---
## Theorems in Foundation
---

-- Implication is a meta-preorder.
instance imp: MetaRelation (⟹).
instance imp: MetaPreorder (⟹);
	- if PQ: P ⟹ Q, QR: Q ⟹ R, P: P then R; apply QR, PQ, P.
	.

note#refl imp.refl.

instance imp: imp.MetaLeftMonotone (⟹);
	- for P if QR: Q ⟹ R, PQ: P ⟹ Q, P: P then R; apply QR PQ P.
	.

lemma mp: if P: P, PQ: P ⟹ Q then Q; apply PQ[OF P].

lemma weaken: if P: P, Q: Q then P; apply P.

lemma ignore: if PQR: (P ⟹ Q) ⟹ R, Q: Q then R; by PQR Q.

lemma imp_imp_sym: if PQR: P ⟹ Q ⟹ R then Q ⟹ P ⟹ R; by PQR.

lemma insert: if PQ: P ⟹ Q, RP: R ⟹ P then R ⟹ Q; by PQ RP.

lemma imp2_imp_imp: if PQQR: ((P ⟹ Q) ⟹ Q) ⟹ R, P! P then R;
	apply PQQR;
	- if PQ: P ⟹ Q then Q; by PQ.
	.

lemma imp_all: if imp: P ⟹ ∀x. Q.[x] then ∀x. P ⟹ Q.[x];
	by imp.

lemma all_indep_imp: if all: ∀x. P ⟹ Q.[x] then P ⟹ ∀x. Q.[x];
	by all.

lemma all_all_imp: if all: ∀x. P.[x], imp: ∀x. P.[x] ⟹ Q.[x] then ∀x. Q.[x];
	by imp all.

lemma obtain_as: for witness if Pw: P.[witness], assm: ∀x. P.[x] ⟹ thesis then thesis;
	by assm[OF Pw].
