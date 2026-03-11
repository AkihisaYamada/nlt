------
# Base
------

begin -- Base doesn't have any axiom

---
## Notations
---

set symbol
	Γ-Δ, Θ, Λ, Ξ, Π, Σ, Φ, Ψ-Ω, α-ξ, π-ω,-- Greek
	ℂ, ℋ, ℍ, ℐ-ℓ, ℕ, ℘-ℝ, ℤ, ℬ-ℭ, ℰ-ℱ, ℵ-ℸ, ℼ-⅀, ⅅ-ⅉ, -- Letterlike Symbols
	𝒜, 𝒞-𝒟, 𝒢, 𝒥-𝒦, 𝒩-𝒬, 𝒮-𝒵, 𝔸-𝔹, 𝔻-𝔾, 𝕀-𝕄, 𝕆, 𝕊-𝕐,𝕒-𝕫, 𝟘-𝟡, -- Mathematical Alphanumeric Symbols
	∀-⋿, -- Mathematical Operators
	⟀-⟯, -- Miscellaneous Mathematical Symbols-A
	←-⇿, -- Arrows
	⟰-⟿, -- Supplemental Arrows-A
	⨀-⫿. -- Supplemental Mathematical Operators

set solo ¬.

infix ⟹ 1 0 0.
binder ∀ 0 0.

infix ⟺ 1 1 0.
infix ∨ 10 11 10.
infix ∧ 20 21 20.
prefix ¬ 30 30.
binder ∃ 0 0.
binder ∃! 0 0.
binder λ 0 0.
binder THE 0 0.
binder SOME 0 0.
binder Π 51 0.

infix ∈ 51 51 50.
syntax ∀ _ ∈ _. _ := ∀∈.
syntax ∃ _ ∈ _. _ := ∃∈.
syntax λ _ ∈ _. _ := λ.∈.
syntax ∃! _ ∈ _. _ := ∃!∈.
syntax THE _ ∈ _. _ := _TheIn.
syntax SOME _ ∈ _. _ := _SomeIn.
syntax Π _ ∈ _. _ := Π.∈.

infix ⊆ 51 51 50.
syntax ∀ _ ⊆ _. _ := ∀⊆.
syntax ∃ _ ⊆ _. _ := ∃⊆.
syntax ∃! _ ⊆ _. _ := ∃!⊆.

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
syntax THE _ < _. _ := _TheLt.
syntax SOME _ < _. _ := _SomeLt.

infix ≤ 51 51 50.
syntax ∀ _ ≤ _. _ := ∀≤.
syntax ∃ _ ≤ _. _ := ∃≤.
syntax ∃! _ ≤ _. _ := ∃!≤.

syntax {_ < _. _} := _CollectLt.


infix > 51 51 50.
infix ≥ 51 51 50.
infix ⊑ 51 51 50.
infix ⊒ 51 51 50.
infix ⊏ 51 51 50.
infix ⊐ 51 51 50.

infix → 61 60 60.

infix + 100 101 100.
infix - 100 101 100.
infix ⋅ 191 190 190.
infix * 200 201 200.
infix / 200 201 200.
infix \ 201 200 200.
infix ^ 300 301 300.

---
## Properties of Untyped Binary Relations
---
theory MetaRelation:
	fix (≤).
end

theory MetaReflexive:
	import MetaRelation.
	assume refl: x ≤ x.
end

theory MetaTransitive:
	import MetaRelation.
	assume trans: if x ≤ y, y ≤ z then x ≤ z.
end

theory MetaPreorder:
	import MetaReflexive.
	import MetaTransitive.
end

theory MetaSymmetric:
	fix (~).
	assume sym: if x ~ y then y ~ x.
begin
	interpret MetaRelation (~).
end

theory MetaTolerance:
	fix (~).
	import MetaReflexive (~).
	import MetaSymmetric.
end

theory MetaPartialEquivalence:
	import MetaSymmetric.
	import MetaTransitive (~).
end

theory MetaEquivalence:
	fix (~).
	import MetaReflexive (~).
	import MetaPartialEquivalence.
begin
	interpret MetaPreorder (~).
	interpret MetaTolerance.
end

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

---
## Properties of Binary Operators and Relations
---
context MetaRelation begin

	theory MetaCompatible:
		fix (*).
		assume cong: if x ≤ x', y ≤ y' then x * y ≤ x' * y'.
	end

	theory MetaCommutative:
		fix (*).
		assume commute: x * y ≤ y * x.
	end

	theory MetaLeftAssociative:
		fix (*) (⋅).
		assume left_assoc: x * y ⋅ z ≤ x ⋅ y ⋅ z.
	end

	theory MetaRightAssociative:
		fix (^) (*).
		assume right_assoc: x ^ (y * z) ≤ x ^ y ^ z.
	end

	theory MetaIdempotent:
		fix (*).
		assume idem: x * x ≤ x.
	end

	theory MetaLeftNeutral:
		fix (*) (1).
		assume left_neutral: 1 * x ≤ x.
	end

	theory MetaRightNeutral:
		fix (*) (1).
		assume right_neutral: x * 1 ≤ x.
	end

	theory MetaNeutral:
		import MetaLeftNeutral.
		import MetaRightNeutral.
	end

	theory MetaLeftAbsorb:
		fix (*) (0).
		assume left_absorb: 0 * x ≤ 0.
	end

	theory MetaRightAbsorb:
		fix (*) (0).
		assume right_absorb: x * 0 ≤ 0.
	end

	theory MetaAbsorb:
		import MetaLeftAbsorb.
		import MetaRightAbsorb.
	end

end

context MetaPartialEquivalence begin

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

	theory MetaLeftNeutral:
		import MetaLeftNeutral.
	begin
		lemma right_neutral_is_neutral: if all: ∀x. x * e ~ x then e ~ 1;
			have 1: e ~ 1 * e;
				apply sym;
				by left_neutral.
			apply trans[OF 1];
			by all.
	end

	theory MetaRightNeutral:
		import MetaRightNeutral.
	begin
		lemma left_neutral_is_neutral: if all: ∀x. e * x ~ x then e ~ 1;
			have 1: e ~ e * 1;
				apply sym;
				by right_neutral.
			apply trans[OF 1];
			by all.
	end

	theory MetaNeutral:
		import MetaNeutral.
	begin
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

	theory MetaLeftAbsorb:
		import MetaLeftAbsorb.
	begin
		lemma right_absorb_is_absorb: if all: ∀x. x * e ~ e then e ~ 0;
			have 1: e ~ 0 * e;
				apply sym;
				by all.
			apply trans[OF 1];
			by left_absorb.
	end

	theory MetaRightAbsorb:
		import MetaRightAbsorb.
	begin
		lemma left_absorb_is_absorb: if all: ∀x. e * x ~ e then e ~ 0;
			have 1: e ~ e * 0;
				apply sym;
				by all.
			apply trans[OF 1];
			by right_absorb.
	end

	theory MetaAbsorb:
		import MetaAbsorb.
	begin
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

theory True:
begin
	obtain true where true_intro! true;
		- for thesis if assm: ∀true. true ⟹ thesis then thesis;
			by assm[of (∀x. x ⟹ x)].
		.
end

theory And:
	fix (∧).
	assume and_intro! for P Q if P, Q then P ∧ Q.
	assume and_elim1: if P ∧ Q then P.
	assume and_elim2: if P ∧ Q then Q.
begin
	lemma and_elim(elim) if PQ: P ∧ Q, PQR: P ⟹ Q ⟹ R then R;
		by PQR and_elim1[OF PQ] and_elim2[OF PQ].
	lemma and_imp_intro: if PQR: P ⟹ Q ⟹ R, PQ: P ∧ Q then R;
		by and_elim[OF PQ PQR].
	interpret and: MetaPartialEquivalence (∧).
end

theory Not:
	fix false (¬).
	assume not_intro: if P ⟹ false then ¬P.
	assume not_imp_false(weak after 1) if ¬P, P then false.
begin
	lemma not_false: ¬false;
		by not_intro.
	lemma false_imp_not: if 0: false then ¬P;
		by not_intro 0.
	lemma imp_not: if P: P, nQ: ¬Q then ¬(P ⟹ Q);
		apply not_intro;
		- if PQ: P ⟹ Q;
			by nQ PQ[OF P].
		.
	lemma imp_not_imp: if PQ: P ⟹ Q then ¬Q ⟹ ¬P;
		by not_intro PQ.
	lemma not_imp_imp_not: if nP: ¬P, QP: Q ⟹ P then ¬Q;
		by imp_not_imp[OF QP nP].
	lemma imp_not_sym: if PnQ: P ⟹ ¬Q then Q ⟹ ¬P;
		by not_intro PnQ(elim).
	lemma nnot_intro: P ⟹ ¬¬P;
		by not_intro.
	lemma nnot_imp: if imp: ¬¬P ⟹ Q then P ⟹ Q;
		by imp nnot_intro.
	lemma not_imp_not_all: ¬P.[x] ⟹ ¬(∀y. P.[y]);
		by not_intro.
	lemma nnot_imp_nnot: if nnP: ¬¬P, PQ: P ⟹ Q then ¬¬Q;
		apply not_intro;
		- if nQ: ¬Q;
			use nnP;
			by imp_not_imp[OF PQ nQ].
		.
	lemma nnot_not_imp_nimp: if nnP: ¬¬P, ! ¬Q then ¬(P ⟹ Q);
		apply not_intro;
		- if PQ: P ⟹ Q;
			by nnot_imp_nnot[OF nnP PQ].
		.
	lemma nnimp_imp_nnot: if nnPQ: ¬¬(P ⟹ Q), P: P then ¬¬Q;
		apply not_intro;
		- if nQ: ¬Q;
			have nPQ: ¬(P ⟹ Q);
				apply not_intro;
				- if PQ: P ⟹ Q;
					by nQ PQ[OF P].
				.
			use nnPQ nPQ.
		.
end

theory AllRel:
	fix (<) (∀<).
	assume all_intro! if ∀x. x < a ⟹ P.[x] then ∀x < a. P.[x].
	assume all_elim1: for x if ∀y < a. P.[y], x < a then P.[x].
begin
	lemma all_elim: if all: ∀x < a. P.[x], imp: (∀x. x < a ⟹ P.[x]) ⟹ Q then Q;
		by imp all_elim1[OF all].
end
