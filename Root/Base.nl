------
# Base
------

begin -- Base doesn't have any axiom

---
## Notations
---
infix ⟹ 1 0 0.
binder ∀ 0 0.

symbol λ ∧ ∨ ∃ ≠ ≤ ≥ ∈ ∋ ⊆ ⊇ ⊂ ⊃ ∩ ∪ ⋂ ⋃ → ⟶ ⟷.
symbol solo ¬.

prefix ¬ 40 40.
infix ∧ 35 36 35.
infix ∨ 30 31 30.
infix ⟺ 1 1 0.
infix ⟶ 1 0 0.
infix ⟷ 1 1 0.
binder ∃ 0 0.
binder ∃! 0 0.
infix : 50 51 50.
binder_middle ∀ : ∀:.
binder_middle ∃ : ∃:.
binder_middle ∀ ∈ ∀∈.
binder_middle ∃ ∈ ∃∈.
binder_middle ∃! ∈ ∃!∈.

binder THE 0 0.
binder SOME 0 0.
binder_middle THE ∈ THE_IN.
binder_middle SOME ∈ SOME_IN.

infix = 51 51 50.
infix ≡ 51 51 50.
infix ≠ 51 51 50.
infix ~ 51 51 50.

binder λ 0 0.

infix ∈ 50 50 50.
infix ∋ 50 50 50.
infix ∉ 50 50 50.
infix ⊆ 51 51 50.
infix ⊂ 51 51 50.
infix ⊇ 51 51 50.
infix ⊃ 51 51 50.
infix ∪ 61 60 61.
infix ∩ 71 70 71.
infix ` 100 100 100.
infix → 61 60 60.

infix < 51 51 50.
infix > 51 51 50.
infix ≤ 51 51 50.
infix ≥ 51 51 50.

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
	assume trans: x ≤ y ⟹ y ≤ z ⟹ x ≤ z.
end

theory MetaSymmetric:
	fix (~).
	assume sym: x ~ y ⟹ y ~ x.
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
namespace imp begin
	interpret MetaPreorder (⟹);
		for P Q R if PQ: P ⟹ Q, QR: Q ⟹ R then P ⟹ R;
			by QR PQ.
		.
end

thm imp.trans.

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
	fix (=).
begin

	theory MetaCompatible:
		fix (*).
		assume cong: for x y x' y', x = x' ⟹ y = y' ⟹ x * y = x' * y'.
	end

	theory MetaCommutative:
		fix (*).
		assume commute: x * y = y * x.
	end

	theory MetaAssociative:
		fix (*).
		assume assoc: x * y * z = x * (y * z).
	end

	theory MetaLeftNeutral:
		fix (*) (1).
		assume left_neutral: 1 * x = x.
	end

	theory MetaRightNeutral:
		fix (*) (1).
		assume right_neutral: x * 1 = x.
	end

	theory MetaLeftAbsorb:
		fix (*) (0).
		assume left_absorb: 0 * x = 0.
	end

	theory MetaRightAbsorb:
		fix (*) (0).
		assume right_absorb: x * 0 = 0.
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

lemma imp2_imp_imp: if PQQR: ((P ⟹ Q) ⟹ Q) ⟹ R, [P] then R;
	apply PQQR;
	if PQ: P ⟹ Q then Q;
		by PQ.
	.

lemma imp_all: if imp: P ⟹ ∀x. α.[x] then ∀x. P ⟹ α.[x];
	for x if P: P;
		by imp[OF P].
	.

lemma all_imp: if all: ∀x. P ⟹ α.[x], [P] then ∀x. α.[x];
	by all.

lemma all_all_imp: if [∀x. α.[x]], imp: ∀x. α.[x] ⟹ β.[x] then ∀x. β.[x];
	by imp.

lemma make_elim:
if imp: ∀x. P.[x] ⟹ Q.[x] then ∀x. P.[x] ⟹ ∀R. (Q.[x] ⟹ R) ⟹ R;
	for x if Px;
		for R if assm;
			by assm imp Px.
		.
	.
