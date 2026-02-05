------
# Base
------

begin -- Base doesn't have any axiom

---
## Notations
---
infix ⟹ 1 0 0.
binder ∀ 0 0.

symbol λ ∧ ∨ ∃ ≠ ≈ ≤ ≥ ∈ ∋ ⊆ ⊇ ⊂ ⊃ ∩ ∪ → × ⋂ ⋃ ⋀ ⋁ ⟶ ⟷ ⊑ ⊒ ⊏ ⊐.
symbol solo ¬.

infix ⟺ 1 1 0.
infix ∨ 10 11 10.
infix ∧ 20 21 20.
prefix ¬ 30 30.
binder ∃ 0 0.
binder ∃! 0 0.
binder λ 0 0.
binder THE 0 0.
binder SOME 0 0.

infix ∈ 51 51 50.
syntax ∀_ ∈ _. _ := ∀∈.
syntax ∃_ ∈ _. _ := ∃∈.
syntax λ_ ∈ _. _ := λ∈.
syntax ∃!_ ∈ _. _ := ∃!∈.
syntax THE _ ∈ _. _ := THE.∈.
syntax SOME _ ∈ _. _ := SOME.∈.

infix ⊆ 51 51 50.
syntax ∀_ ⊆ _. _ := ∀⊆.
syntax ∃_ ⊆ _. _ := ∃⊆.
syntax ∃!_ ⊆ _. _ := ∃!⊆.

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
syntax ∀_ < _. _ := ∀<.
syntax ∃_ < _. _ := ∃<.
syntax ∃!_ < _. _ := ∃!<.

infix ≤ 51 51 50.
syntax ∀_ ≤ _. _ := ∀≤.
syntax ∃_ ≤ _. _ := ∃≤.
syntax ∃!_ ≤ _. _ := ∃!≤.

infix > 51 51 50.
infix ≥ 51 51 50.
infix ⊑ 51 51 50.
infix ⊒ 51 51 50.
infix ⊏ 51 51 50.
infix ⊐ 51 51 50.

infix → 61 60 60.
infix ∪ 71 70 71.
infix ∩ 81 80 81.
infix ` 101 100 100.
infix × 111 110 110.

infix + 100 101 100.
infix - 100 101 100.
infix * 110 111 110.
infix / 110 111 110.
infix \ 111 111 110.

---
## Properties of Untyped Binary Relations
---
theory MetaReflexive:
	fix (≤).
	assume refl: x ≤ x.
end

theory MetaTransitive:
	fix (≤).
	assume trans: if x ≤ y, y ≤ z then x ≤ z.
end

theory MetaSymmetric:
	fix (~).
	assume sym: if x ~ y then y ~ x.
end

theory MetaPreorder:
	import MetaReflexive.
	import MetaTransitive.
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
	import MetaSymmetric.
	import MetaTransitive (~).
begin
	interpret MetaPreorder (~).
	interpret MetaTolerance.
	interpret MetaPartialEquivalence.
end

-- Implication is a meta-preorder.
namespace imp:
	interpret MetaPreorder (⟹);
		- if PQ: P ⟹ Q, QR: Q ⟹ R then P ⟹ R;
			by QR PQ.
		.
end

lemma mp: if P: P, PQ: P ⟹ Q then Q;
by PQ[OF P].

lemma weaken: if P: P, Q: Q then P;
by P.

lemma ignore: if PQR: (P ⟹ Q) ⟹ R, Q: Q then R;
by PQR Q.

---
## Properties of Binary Operators and Relations
---
theory MetaMagmas:
	fix (~).
begin

	theory MetaCompatible:
		fix (*).
		assume cong: if x ~ x', y ~ y' then x * y ~ x' * y'.
	end

	theory MetaCommutative:
		fix (*).
		assume commute: x * y ~ y * x.
	end

	theory MetaAssociative:
		fix (*).
		assume assoc: x * y * z ~ x * (y * z).
	end

	theory MetaIdempotent:
		fix (*).
		assume idem: x * x ~ x.
	end

	theory MetaLeftNeutral:
		fix (*) (1).
		assume left_neutral: 1 * x ~ x.
	end

	theory MetaRightNeutral:
		fix (*) (1).
		assume right_neutral: x * 1 ~ x.
	end

	theory MetaLeftAbsorb:
		fix (*) (0).
		assume left_absorb: 0 * x ~ 0.
	end

	theory MetaRightAbsorb:
		fix (*) (0).
		assume right_absorb: x * 0 ~ 0.
	end

end

context MetaTransitive begin

	interpret MetaMagmas (≤).

	theory MetaCommNeutral:
		import MetaLeftNeutral.
		import MetaCommutative.
	begin
		interpret MetaRightNeutral;
			by trans[OF commute left_neutral].
	end

	theory MetaCommAbsorb:
		import MetaLeftAbsorb.
		import MetaCommutative.
	begin
		interpret MetaRightAbsorb;
			by trans[OF commute left_absorb].
	end

	theory MetaCommMonoid:
		import MetaCommNeutral.
		import MetaAssociative.
	end

	theory MetaCommMonoidAbsorb:
		fix (*) (0) (1).
		import MetaCommMonoid.
		import MetaCommAbsorb.
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

lemma imp_all: if imp: P ⟹ ∀x. Q.[x], P: P then Q.[x];
	by imp[OF P].

lemma all_imp: if all: ∀x. P ⟹ Q.[x], P! P then ∀x. Q.[x];
	by all.

lemma all_all_imp: if [∀x. P.[x]], imp: ∀x. P.[x] ⟹ Q.[x] then ∀x. Q.[x];
	by imp.

lemma make_elim:
	if PQ: ∀x. P.[x] ⟹ Q.[x], P: P.[x], QR: Q.[x] ⟹ R then R;
	by QR PQ P.

theory Ex:
	fix (∃).
	assume ex_intro1: for x P if P.[x] then ∃x. P.[x].
	assume ex_elim: if ∃x. P.[x], ∀x. P.[x] ⟹ Q then Q.
begin
	lemma ex_intro: if assm: ∀Q. (∀x. P.[x] ⟹ Q) ⟹ Q then ∃x. P.[x];
		apply assm;
		- for x;
			by ex_intro1[of x].
		.
end

theory AllRel:
	fix (∀<) (<).
	assume intro! if ∀x. x < A ⟹ P.[x] then ∀x < A. P.[x].
	assume elim1: if ∀x < A. P.[x], x < A then P.[x].
begin
	lemma elim: if all: ∀x < A. P.[x], imp: (∀x. x < A ⟹ P.[x]) ⟹ Q then Q;
		by imp elim1[OF all].
end

theory ExRel:
	fix (∃<) (<).
	assume intro1: for x if x < A, P.[x] then ∃x < A. P.[x].
	assume elim: if ∃x < A. P.[x], ∀x. x < A ⟹ P.[x] ⟹ Q then Q.
begin
	lemma intro: if assm: ∀Q. (∀x. x < A ⟹ P.[x] ⟹ Q) ⟹ Q then ∃x < A. P.[x];
		apply assm;
		- for x;
			by intro1[of x].
		.
end