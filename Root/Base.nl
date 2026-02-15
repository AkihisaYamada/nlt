------
# Base
------

begin -- Base doesn't have any axiom

---
## Notations
---
infix ⟹ 1 0 0.
binder ∀ 0 0.

symbol λ ∧ ∨ ∃ ≠ ≈ ≤ ≥ ∈ ∋ ⊆ ⊇ ⊂ ⊃ ∩ ∪ → × ⋅ ∘ • ⋂ ⋃ ⋀ ⋁ ⟶ ⟷ ⊑ ⊒ ⊏ ⊐.
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
syntax THE _ ∈ _. _ := _TheIn.
syntax SOME _ ∈ _. _ := _SomeIn.

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
syntax THE _ < _. _ := _TheLt.
syntax SOME _ < _. _ := _SomeLt.

infix ≤ 51 51 50.
syntax ∀_ ≤ _. _ := ∀≤.
syntax ∃_ ≤ _. _ := ∃≤.
syntax ∃!_ ≤ _. _ := ∃!≤.

syntax {} := _empty.
syntax {_} := _singleton.
syntax {_. _} := _Collect.
syntax {_ ∈ _. _} := _CollectIn.


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

	theory MetaLeftAbsorb:
		fix (*) (0).
		assume left_absorb: 0 * x ≤ 0.
	end

	theory MetaRightAbsorb:
		fix (*) (0).
		assume right_absorb: x * 0 ≤ 0.
	end

end

context MetaSymmetric begin

	theory MetaAssociative:
		fix (*).
		import MetaLeftAssociative (*) (*).
	begin
		interpret MetaRightAssociative (*) (*);
			- for x y z;
				apply sym;
				by left_assoc.
			.
	end

end

context MetaTransitive begin

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
	lemma not_imp_not: if nP: ¬P, QP: Q ⟹ P then ¬Q;
		by not_intro not_imp_false[OF nP] QP.
	lemma imp_not: if P: P, nQ: ¬Q then ¬(P ⟹ Q);
		apply not_intro;
		- if PQ: P ⟹ Q;
			by nQ PQ[OF P].
		.
	lemma imp_not_imp: if PQ: P ⟹ Q then ¬Q ⟹ ¬P;
		by not_intro PQ.
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
	fix (<) (∀<).
	assume all_intro! if ∀x. x < a ⟹ P.[x] then ∀x < a. P.[x].
	assume all_elim1: if ∀x < a. P.[x], x < a then P.[x].
begin
	lemma all_elim: if all: ∀x < a. P.[x], imp: (∀x. x < a ⟹ P.[x]) ⟹ Q then Q;
		by imp all_elim1[OF all].
end

theory ExRel:
	fix (<) (∃<).
	assume ex_intro1: for x if x < A, P.[x] then ∃x < A. P.[x].
	assume ex_elim: if ∃x < A. P.[x], ∀x. x < A ⟹ P.[x] ⟹ Q then Q.
begin
	lemma ex_intro: if assm: ∀Q. (∀x. x < A ⟹ P.[x] ⟹ Q) ⟹ Q then ∃x < A. P.[x];
		apply assm;
		- for x;
			by ex_intro1[of x].
		.
end
