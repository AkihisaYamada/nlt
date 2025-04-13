------
# The Root File
------

begin -- Root doesn't have any axiom

symbol λ ∧ ∨ ∃ ≠ ≤ ∈ ∋ ⊆ ⊇ ⊂ ⊃ ∩ ∪ ⋂ ⋃ →.
symbol solo ¬.

infix ⟹ 1 0 0.
binder ∀ 0 0.

prefix ¬ 40 40.
infix ∧ 35 36 36.
infix ∨ 30 31 30.
infix ⟺ 1 1 0.
binder ∃ 0 0.
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
	show: for P Q R, if PQ: P ⟹ Q, QR: Q ⟹ R then P ⟹ R;
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
	- for x, if P: P;
		by imp[OF P].
	.

lemma all_imp: if all: ∀x. P ⟹ α.[x], [P] then ∀x. α.[x];
	by all.

lemma all_all_imp: if [∀x. α.[x]], imp: ∀x. α.[x] ⟹ β.[x] then ∀x. β.[x];
	by imp.

-- Obtains true, which is provable.
theory True:
	obtain true where true_intro! true;
		- for thesis, if assm: ∀true. true ⟹ thesis;
			by assm[of (∀x. x ⟹ x)].
		.
end

-- Obtains false, which derives everything, including non-propositions.
theory False:
	obtain false where false_elim: false ⟹ ∀P. P;
		- for thesis, if assm: ∀false. (false ⟹ ∀P. P) ⟹ thesis then thesis;
			by assm[of (∀P. P)].
		.
end


-----
## For typed logic
-----

theory Member:
	fix mem c.
	assume type: mem c.
end

theory Unary:
	fix f dom cod.
	assume type: dom x ⟹ cod (f x).
end

theory Binary:
	fix f dom1 dom2 cod.
	assume type: dom1 x ⟹ dom2 y ⟹ cod (f x y).
end

theory Reflexive:
	fix mem (≤).
	assume refl: mem x ⟹ x ≤ x.
end

theory Symmetric:
	fix mem (≤).
	assume sym: x ≤ y ⟹ mem x ⟹ mem y ⟹ y ≤ x.
end

theory Transitive:
	fix mem (≤).
	assume trans: x ≤ y ⟹ y ≤ z ⟹ mem x ⟹ mem y ⟹ mem z ⟹ x ≤ z.
end

theory Irreflexive:
	fix mem (<) (¬).
	assume irrefl: mem x ⟹ ¬ (x < x).
end

theory Binder:
	fix mem ξ.
	assume type: (∀x. mem α.[x]) ⟹ mem (ξ (x. α.[x])).
end

theory TypedBinder:
	fix mem ξ.
	assume type: (∀x. ι x ⟹ mem α.[x]) ⟹ mem (ξ ι (x. α.[x])).
end

theory Magma:
	fix mem (+).
	import Binary (+) mem mem mem.
end

theory Commutative:
	fix mem (+) (=).
	assume commute: mem x ⟹ mem y ⟹ x + y = y + x.
end

theory Associative:
	fix mem (+) (=).
	assume assoc: mem x ⟹ mem y ⟹ mem z ⟹ x + y + z = x + (y + z).
end

theory LeftNeutral:
	fix mem (+) (0) (=).
	assume left_neutral: mem x ⟹ 0 + x = x.
end

theory RightNeutral:
	fix mem (+) (0) (=).
	assume right_neutral: mem x ⟹ x + 0 = x.
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
	fix mem (*) (0) (=).
	assume left_absorb: mem x ⟹ 0 * x = 0.
end

theory RightAbsorb:
	fix mem (*) (0) (=).
	assume right_absorb: mem x ⟹ x * 0 = 0.
end

theory If:
	fix (if) (then) (else) (=) (¬).
	assume if: P ⟹ (if P then t else e) = t.
	assume if_not: ¬P ⟹ (if P then t else e) = e.
end

lemma make_elim:
	if imp: ∀x. P.[x] ⟹ Q.[x]
	then ∀x. P.[x] ⟹ ∀thesis. (Q.[x] ⟹ thesis) ⟹ thesis;
	- for x, if Px;
		- for thesis, if assm;
			by assm imp Px.
		.
	.

theory Collect:
	fix Collect (∈).
	assume Collect_elim1: x ∈ Collect P ⟹ P x.
	assume Collect_intro: P x ⟹ x ∈ Collect P.
begin
	note Collect_elim: make_elim[of (x. x ∈ Collect P) (x. P x), OF Collect_elim1].
end

theory FunType:
	fix (→).
	assume fun_type_elim1: (σ → τ) f ⟹ ∀a. σ a ⟹ τ (f a).
	assume fun_type_intro! (∀a. σ a ⟹ τ (f a)) ⟹ (σ → τ) f.
begin
	note fun_type_elim: make_elim[of (f. (σ → τ) f) (f. ∀a. σ a ⟹ τ (f a)), OF fun_type_elim1].
end

theory Prop:
	fix prop.
	import imp: Magma prop (⟹).
begin
	note! imp.type.
end

theory TypedTrue:
	fix prop true.
	import true: Member prop true.
	assume true_intro: true.
end

theory TypedFalse:
	fix prop false.
	import false: Member prop false.
	assume false_elim: false ⟹ ∀P. prop P ⟹ P.
end

theory TypedAll:
	fix prop (∀:).
	import Prop.
	import all: TypedBinder prop (∀:).
	assume all_intro: (∀x. ι x ⟹ α.[x]) ⟹ (∀x. ι x ⟹ prop α.[x]) ⟹ ∀x:ι. α.[x].
	assume all_elim1: for x, (∀y:ι. α.[y]) ⟹ ι x ⟹ (∀y. ι y ⟹ prop α.[y]) ⟹ α.[x].
begin
	note! all.type.
	interpret TypedTrue;
		obtain true where ! prop true, ! true;
			- for thesis, if assm;
				apply assm[of (∀P:prop. P ⟹ P)];
				by all_intro.
			.
		.
end

theory TypedEx:
	fix prop (∃:).
	import Prop.
	import ex: TypedBinder prop (∃:).
	assume ex_intro1: for x, α.[x] ⟹ ι x ⟹ (∀y. ι y ⟹ prop α.[y]) ⟹ ∃y:ι. α.[y].
	assume ex_elim: (∃x:ι. α.[x]) ⟹ ∀P. (∀x. α.[x] ⟹ ι x ⟹ P) ⟹
	(∀x. ι x ⟹ prop α.[x]) ⟹ prop P ⟹ P.
end

