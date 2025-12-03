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

theory MetaLeftAbsorb:
	fix (*) (0) (=).
	assume left_absorb: 0 * x = 0.
end

theory MetaRightAbsorb:
	fix (*) (0) (=).
	assume right_absorb: x * 0 = 0.
end

---
theory MetaUnitalCommutative (+) (0) (=):
	import MetaEquivalence;
	import MetaCommutative;
	import MetaLeftNeutral;
	interpret right: MetaNeutral;
		discharge x + 0 = x;
			
---
interpret imp: MetaPreorder;
	instantiate (≤) := (⟹).
	- for P Q R if PQ: P ⟹ Q, QR: Q ⟹ R then P ⟹ R;
		by QR PQ.
	.

lemma imp_commute: if PQR: P ⟹ Q ⟹ R then Q ⟹ P ⟹ R;
	by PQR.

lemma insert: if PQ: P ⟹ Q, RP: R ⟹ P then R ⟹ Q;
	by PQ RP.

lemma imp2_imp_imp: if PQQR: ((P ⟹ Q) ⟹ Q) ⟹ R, [P] then R;
	apply PQQR;
	- if PQ: P ⟹ Q then Q;
		by PQ.
	.

lemma imp_all: if imp: P ⟹ ∀x. α.[x] then ∀x. P ⟹ α.[x];
	- for x if P: P;
		by imp[OF P].
	.

lemma all_imp: if all: ∀x. P ⟹ α.[x], [P] then ∀x. α.[x];
	by all.

lemma all_all_imp: if [∀x. α.[x]], imp: ∀x. α.[x] ⟹ β.[x] then ∀x. β.[x];
	by imp.

lemma make_elim:
	if imp: ∀x. P.[x] ⟹ Q.[x]
	then ∀x. P.[x] ⟹ ∀thesis. (Q.[x] ⟹ thesis) ⟹ thesis;
	- for x if Px;
		- for thesis if assm;
			by assm imp Px.
		.
	.

-----
## For typed logic
-----

theory Member:
	fix σ x (:).
	assume type: x : σ.
end

theory Unary:
	fix σ τ f (:).
	assume type: x : σ ⟹ f x : τ.
end

theory Binary:
	fix σ τ ρ f (:).
	assume type: x : σ ⟹ y : τ ⟹ f x y : ρ.
end

theory Relation:
	fix σ (≤) (:) prop.
	import Binary σ σ prop (≤) (:).
end

theory Reflexive:
	fix σ (≤) (:).
	assume refl: x : σ ⟹ x ≤ x.
end

theory Symmetric:
	fix σ (≤) (:).
	assume sym: x ≤ y ⟹ x : σ ⟹ y : σ ⟹ y ≤ x.
end

theory Transitive:
	fix σ (≤) (:).
	assume trans: x ≤ y ⟹ y ≤ z ⟹ x : σ ⟹ y : σ ⟹ z : σ ⟹ x ≤ z.
end

theory Irreflexive:
	fix σ (<) (:) (¬).
	assume irrefl: x : σ ⟹ ¬ (x < x).
end

theory TypedBinder:
	fix σ ξ (:).
	assume type: (∀x. x : ι ⟹ α.[x] : σ) ⟹ ξ ι (x. α.[x]) : σ.
end

theory Magma:
	fix σ (+) (:).
	import Binary σ σ σ (+).
end

theory Commutative:
	fix σ (+) (:) (=).
	assume commute: x : σ ⟹ y : σ ⟹ x + y = y + x.
end

theory Associative:
	fix σ (+) (:) (=).
	assume assoc: x : σ ⟹ y : σ ⟹ z : σ ⟹ x + y + z = x + (y + z).
end

theory LeftNeutral:
	fix σ (+) (0) (:) (=).
	assume left_neutral: x : σ ⟹ 0 + x = x.
end

theory RightNeutral:
	fix σ (+) (0) (:) (=).
	assume right_neutral: x : σ ⟹ x + 0 = x.
end

theory UnitalMagma:
	import Magma.
	import LeftNeutral.
	import RightNeutral.
end

theory Semigroup:
	import Magma.
	import Associative.
end

theory Monoid:
	import Semigroup.
	import UnitalMagma.
end

theory LeftAbsorb:
	fix σ (*) (0) (:) (=).
	assume left_absorb: x : σ ⟹ 0 * x = 0.
end

theory RightAbsorb:
	fix σ (*) (0) (:) (=).
	assume right_absorb: x : σ ⟹ x * 0 = 0.
end

theory AbsorbMagma:
	fix σ (*) (0) (:) (=).
	import Magma σ (*).
	import LeftAbsorb.
	import RightAbsorb.
end

theory TypedAll:
	fix (∀:) prop (:).
	assume imp_type! P : prop ⟹ Q : prop ⟹ (P ⟹ Q) : prop.
	assume all_type! (∀x. x : ι ⟹ α.[x] : prop) ⟹ (∀x : ι. α.[x]) : prop.
	assume all_intro: (∀x. x : ι ⟹ α.[x]) ⟹ (∀x. x : ι ⟹ α.[x] : prop) ⟹ ∀x:ι. α.[x].
	assume all_elim1: for x, (∀y:ι. α.[y]) ⟹ x : ι ⟹ (∀y. y : ι ⟹ α.[y] : prop) ⟹ α.[x].
begin
	lemma all_elim:
		if all: ∀x:ι. α.[x]
		then ∀P. ((∀x. x: ι ⟹ α.[x]) ⟹ P) ⟹ (∀y. y : ι ⟹ α.[y] : prop) ⟹ P;
		- for P if assm, !;
			apply assm;
			- for x if !;
				apply all_elim1[OF all, of x].
			.
		.
	obtain true where true_type! true : prop, true_intro! true;
		- for thesis if assm;
			apply assm[of (∀P:prop. P ⟹ P)];
			by all_intro.
		.
end

theory FunType:
	fix (:) (→).
	assume fun_type_elim1: f : σ → τ ⟹ ∀a. a : σ ⟹ f a : τ.
	assume fun_type_intro! for f σ τ, (∀a. a : σ ⟹ f a : τ) ⟹ f : σ → τ.
begin
	note fun_type_elim: make_elim[of (f. f : σ → τ) (f. ∀a. a : σ ⟹ f a : τ), OF fun_type_elim1].
end

theory Collect:
	fix Collect (∈).
	assume Collect_elim1: x ∈ Collect P ⟹ P x.
	assume Collect_intro: P x ⟹ x ∈ Collect P.
begin
	note Collect_elim: make_elim[of (x. x ∈ Collect P) (x. P x), OF Collect_elim1].
end

