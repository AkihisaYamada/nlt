------
# The Root File
------

begin -- Root doesn't have any axiom

symbol λ ∧ ∨ ∃ ≠ ≤ ∈ ∋ ⊆ ⊇ ⊂ ⊃ ∩ ∪ ⋂ ⋃ →.
symbol solo ¬.

infix ⟹ 1 0 0.
binder ∀ 0 0.

prefix ¬ 40 40.
infix ∧ 35 36 35.
infix ∨ 30 31 30.
infix ⟺ 1 1 0.
binder ∃ 0 0.
infix : 50 51 50.
binder_middle ∀ : ∀:.
binder_middle ∃ : ∃:.
binder_middle ∀ ∈ ∀∈.
binder_middle ∃ ∈ ∃∈.

binder THE 0 0.
binder SOME 0 0.

infix = 51 51 50.
infix ≠ 51 51 50.

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
infix * 110 111 110.

lemma mp: if P: P, PQ: P ⟹ Q then Q;
	by PQ[OF P].

lemma weaken: if P: P, Q: Q then P;
	by P.

lemma ignore: if PQR: (P ⟹ Q) ⟹ R, Q: Q then R;
	by PQR Q.

theory MetaReflexive:
	fix (≤).
	assume refl: x ≤ x.
end

theory MetaTransitive:
	fix (≤).
	assume trans: x ≤ y ⟹ y ≤ z ⟹ x ≤ z.
end

theory MetaPreorder:
	import MetaReflexive.
	import MetaTransitive.
end

theory MetaSymmetric:
	fix (=).
	assume sym: x = y ⟹ y = x.
end

theory MetaEquivalence:
	fix (=).
	import MetaSymmetric.
	import MetaPreorder (=).
end

theory MetaCommutative:
	fix (+) (=).
	assume commute: x + y = y + x.
end

theory MetaAssociative:
	fix (+) (=).
	assume assoc: x + y + z = x + (y + z).
end

theory MetaLeftNeutral:
	fix (+) (0) (=).
	assume left_neutral: 0 + x = x.
end

theory MetaRightNeutral:
	fix (+) (0) (=).
	assume right_neutral: x + 0 = x.
end

theory MetaUnitalCommutative:
	fix (+) (0) (=).
	import MetaEquivalence.
	import MetaCommutative.
	import MetaLeftNeutral.
	interpret MetaRightNeutral;
		by trans[OF commute left_neutral].
end

theory MetaLeftAbsorb:
	fix (*) (0) (=).
	assume left_absorb: 0 * x = 0.
end

theory MetaRightAbsorb:
	fix (*) (0) (=).
	assume right_absorb: x * 0 = 0.
end

interpret imp: MetaPreorder;
	instantiate (≤) := (⟹).
	for P Q R if PQ: P ⟹ Q, QR: Q ⟹ R then P ⟹ R;
		by QR PQ.
	.

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
	if imp: ∀x. P.[x] ⟹ Q.[x]
	then ∀x. P.[x] ⟹ ∀thesis. (Q.[x] ⟹ thesis) ⟹ thesis;
	for x if Px;
		for thesis if assm;
			by assm imp Px.
		.
	.
