import Iff.
import And.
import Not.

begin

---
## Obtaining True
---
obtain true where true_intro! true;
	- for thesis if assm;
		apply assm[of (∀x. x ⟹ x)].
	.

interpret imp: iff.MetaLeftNeutral (⟹) true;
	by imp_imp_iff.

interpret imp: iff.MetaRightAbsorb (⟹) true;
	by iff_intro.

interpret iff: iff.MetaCommNeutral (⟺) true;
	goals.
	by iff_intro #elim iff_elim.

note(simp) imp.left_neutral imp.right_absorb iff.left_neutral iff.right_neutral.

lemma iff_true: P ⟹ P ⟺ true.

---
## Conjunction
---	
interpret and: iff.MetaCompatible (∧);
	- if P: P ⟺ P', Q: Q ⟺ Q' then P ∧ Q ⟺ P' ∧ Q';
		by iff_intro #unfold P Q.
	.
note(cong) and.cong.

interpret and: iff.MetaIdempotent (∧);
	by iff_intro.

interpret and: iff.MetaAssociative (∧);
	by iff_intro.

interpret and: iff.MetaCommNeutral (∧) true;
	by iff_intro.

note(simp) and.left_neutral and.right_neutral.

lemma and_cong1: if P: P ⟺ P', Q: P' ⟹ Q ⟺ Q' then P ∧ Q ⟺ P' ∧ Q';
	by iff_intro #unfold P Q.

lemma and_imp_iff_imp_imp(simp) (P ∧ Q ⟹ R) ⟺ (P ⟹ Q ⟹ R);
	by iff_intro.

lemma imp_and_iff1: if P: P then P ∧ Q ⟺ Q;
	by iff_intro P.

lemma imp_and_iff2: if Q: Q then P ∧ Q ⟺ P;
	by iff_intro Q.

lemma and_iff: P ∧ Q ⟺ (∀R. (P ⟹ Q ⟹ R) ⟹ R);
	apply iff_intro;
	- simp imp_imp_iff.
	- if assm;
		apply assm.
	.

lemma iff_iff_and: (P ⟺ Q) ⟺ (P ⟹ Q) ∧ (Q ⟹ P);
	by iff_intro #elim iff_elim.

lemma imp_and_distrib: (P ⟹ Q ∧ R) ⟺ (P ⟹ Q) ∧ (P ⟹ R);
	apply iff_intro;
	- if imp;
		apply and_intro;
		- if P;
			apply and_elim[OF imp[OF P]].
		- if P;
			apply and_elim[OF imp[OF P]].
		.
	.

lemma all_and_distrib: (∀x. P.[x] ∧ Q.[x]) ⟺ (∀x. P.[x]) ∧ (∀x. Q.[x]);
	apply iff_intro;
	- if ab: ∀x. P.[x] ∧ Q.[x];
		apply and_intro;
		- by and_elim1[OF ab].
		- by and_elim2[OF ab].
		.
	.

---
## Negation
---
lemma not_iff_imp_false: ¬P ⟺ (P ⟹ false);
	apply iff_intro;
	- apply not_imp_false>0.
	- apply not_intro>0.
	.

lemma imp_not_imp_false: if P: P, nP: ¬P then false;
	apply not_imp_false[OF nP P].

lemma imp_not_iff_false: if P: P then ¬P ⟺ false;
	simp not_iff_imp_false iff_true[OF P].

lemma not_cong(cong) if PQ: P ⟺ Q then ¬P ⟺ ¬Q;
	unfold not_iff_imp_false PQ.

lemma imp_not_commute: (P ⟹ ¬Q) ⟺ (Q ⟹ ¬P);
	by iff_intro[OF imp_not_sym imp_not_sym].

lemma nnnot_iff: ¬¬¬P ⟺ ¬P;
	unfold+ not_iff_imp_false;
	by imp3_iff.

lemma nnot_imp_not_iff: (¬¬P ⟹ ¬Q) ⟺ (P ⟹ ¬Q);
	unfold imp_not_commute;
	unfold nnnot_iff.

lemma nnimp_not_iff: ¬¬(P ⟹ ¬Q) ⟺ (P ⟹ ¬Q);
	apply iff_intro;
	- if nnimp: ¬¬(P ⟹ ¬Q), P: P then ¬Q;
		by nnimp_imp_nnot[OF nnimp P, unfold nnnot_iff].
	by nnot_intro.

lemma not_false_iff(simp) ¬false ⟺ true;
	by not_false.

lemma not_true_iff(simp) ¬true ⟺ false;
	unfold not_iff_imp_false.

---
## Negation and Conjunction
---

lemma nand_intro1: if nP: ¬P then ¬(P ∧ Q);
	by not_intro not_imp_false[OF nP].

lemma nand_intro2: if nQ: ¬Q then ¬(P ∧ Q);
	by not_intro not_imp_false[OF nQ].

lemma nand_iff_imp_not: ¬(P ∧ Q) ⟺ (P ⟹ ¬Q);
	simp not_iff_imp_false.

lemma non_contradiction: ¬(P ∧ ¬P);
	unfold nand_iff_imp_not;
	by nnot_intro.

lemma false_nand: ¬(false ∧ P);
	simp not_iff_imp_false.

lemma nand_false: ¬(P ∧ false);
	simp not_iff_imp_false.
	
lemma nand_nnot_iff: ¬(P ∧ ¬¬Q) ⟺ ¬(P ∧ Q);
	unfold+ nand_iff_imp_not nnnot_iff.

lemma nnot_nand_iff: ¬(¬¬P ∧ Q) ⟺ ¬(P ∧ Q);
	unfold and.commute;
	unfold nand_nnot_iff;
	unfold and.commute.

lemma nnand_iff: ¬¬(P ∧ Q) ⟺ ¬¬P ∧ ¬¬Q;
	apply iff_intro;
	- if nnand;
		apply+ and_intro nnand[THEN not_imp_not];
		by #weak nand_intro1 nand_intro2.
	fold nnot_nand_iff;
	by #unfold imp_and_iff1.

lemma not_nniff_not: ¬¬(¬P ⟺ ¬Q) ⟺ (¬P ⟺ ¬Q);
	unfold[at 0] iff_iff_and;
	unfold nnand_iff;
	unfold nnimp_not_iff;.

---
## Double negation and universal quantification.

The following direction is provable in general, but the opposite direction requires something similar to the axiom of choice.
---
lemma nnall_imp: if nnall: ¬¬(∀x. P.[x]) for x then ¬¬P.[x];
	apply not_intro;
	- if nPx: ¬P.[x];
		by not_imp_false[OF nnall] not_imp_not_all[OF nPx].
	.

---
The other direction is provable if inside the quantification has negation.
---
lemma nnall_not_iff: ¬¬(∀x. ¬P.[x]) ⟺ (∀x. ¬P.[x]);
	apply iff_intro;
	- if 1;
		by 1[THEN nnall_imp, unfold nnnot_iff].
	by nnot_intro.

---
## Theories

The logical operators allow us to define some properties.
---
theory MetaIrreflexive:
	fix (<).
	assume irrefl: ¬ x < x.
end

theory MetaAsymmetric:
	fix (<).
	assume asym: x < y ⟹ ¬ y < x.
end
---
Note that antisymmetry is not yet definable, because it requires equality.
---
theory MetaOrder:
	import MetaIrreflexive.
	import MetaTransitive (<).
begin
	interpret MetaAsymmetric;
		- for x y if xy: x < y then ¬ y < x;
			apply not_intro;
			- if yx: y < x;
				have xx: x < x;
					by trans[OF xy yx].
				by not_imp_false[OF irrefl xx].
			.
		.
end

theory AllRel:
	import AllRel.
begin
	lemma all_and_distrib: (∀x < a. P.[x] ∧ Q.[x]) ⟺ (∀x < a. P.[x]) ∧ (∀x < a. Q.[x]);
		simp all_def all_and_distrib imp_and_distrib.
print.
	lemma not_imp_not_all: if nP: ¬P.[x], x: x < a then ¬(∀y < a. P.[y]);
		apply not_intro;
		- if all;
			use nP all_elim1[OF all x].
		.
	lemma nnall_imp: if nnall: ¬¬(∀x < a. P.[x]) then ∀x < a. ¬¬P.[x];
		apply all_intro;
		- if x: x < a;
			apply not_intro;
			- if nPx: ¬P.[x];
				by not_imp_false[OF nnall] not_imp_not_all[OF nPx] x.
			.
		.
	lemma nnall_not_iff: ¬¬(∀x < a. ¬P.[x]) ⟺ (∀x < a. ¬P.[x]);
		apply iff_intro;
		- if 1;
			by all_cong_weak(cong) 1[THEN nnall_imp, unfold nnnot_iff].
		by nnot_intro.
end

theory Membership:
	import ..Membership.
	import in: .AllRel (∈) (∀∈).
	fix (⊆).
	assume subseteq_iff_allIn: A ⊆ B ⟺ (∀x ∈ A. x ∈ B).
	import sub: .AllRel (⊆) (∀⊆).
begin
	note! in.all_intro.
end

theory RestrictedComprehension:
	import Membership.
	fix _CollectIn.
	assume in_CollectIn_iff: x ∈ {x ∈ A. P.[x]} ⟺ x ∈ A ∧ P.[x].
begin

end
