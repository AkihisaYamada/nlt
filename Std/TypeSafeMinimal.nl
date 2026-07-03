fix false (∧) (∨) (¬) (⟺) (∃).

import And.
import Not.
import Iff.

assume or_intro1: for P Q if P then P ∨ Q.
assume or_intro2: for P Q if Q then P ∨ Q.

assume ex_intro1: for x if P.[x] then ∃x. P.[x].

begin

---
## True
---
obtain true where true_intro! true;
	- for thesis if assm: ∀true. true ⟹ thesis then thesis;
		by assm[of (∀x. x ⟹ x)].
	.

interpret imp: iff.MetaLeftNeutral (⟹) true;
	by imp_imp_iff.

interpret imp: iff.MetaRightAbsorb (⟹) true;
	by iff_intro.

interpret iff: iff.MetaCommNeutral (⟺) true;
	by iff_intro #elim iff_elim.

note#simp imp.left_neutral imp.right_absorb iff.left_neutral iff.right_neutral.

lemma iff_true: P ⟹ P ⟺ true.

---
## Conjunction
---	
interpret and: iff.MetaCompatible (∧);
	- if P: P ⟺ P', Q: Q ⟺ Q' then P ∧ Q ⟺ P' ∧ Q';
		by iff_intro #simp P Q.
	.

lemma and_cong1#cong if P: P ⟺ P', Q: P' ⟹ Q ⟺ Q' then P ∧ Q ⟺ P' ∧ Q';
	by iff_intro #simp P Q.

interpret and: iff.MetaIdempotent (∧);
	by iff_intro.

interpret and: iff.MetaCommMonoid (∧) true;
	by iff_intro.

note #simp and.left_neutral and.right_neutral.

lemma and_imp_iff_imp_imp#simp#rule (P ∧ Q ⟹ R) ⟺ (P ⟹ Q ⟹ R);
	by iff_intro.

lemma imp_and_iff1#simp if P: P then P ∧ Q ⟺ Q;
	by iff_intro P.

lemma imp_and_iff2#simp if Q: Q then P ∧ Q ⟺ P;
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
lemma not_iff_imp_false#rule ¬ P ⟺ (P ⟹ false);
	apply iff_intro;
	- apply not_imp_false>0.
	- apply not_intro>0.
	.

lemma imp_not_imp_false: if P: P, nP: ¬ P then false;
	apply not_imp_false[OF nP P].

lemma imp_not_iff_false: if P: P then ¬ P ⟺ false;
	simp not_iff_imp_false iff_true[OF P].

lemma not_cong#cong if PQ: P ⟺ Q then ¬ P ⟺ ¬ Q;
	unfold not_iff_imp_false PQ.

lemma imp_not_commute: (P ⟹ ¬ Q) ⟺ (Q ⟹ ¬ P);
	by iff_intro[OF imp_not_sym imp_not_sym].

lemma nnnot_iff: ¬ ¬ ¬ P ⟺ ¬ P;
	unfold+ not_iff_imp_false;
	by imp3_iff.

lemma nnot_imp_not_iff: (¬ ¬ P ⟹ ¬ Q) ⟺ (P ⟹ ¬ Q);
	unfold imp_not_commute;
	unfold nnnot_iff.

lemma nnimp_not_iff: ¬ ¬ (P ⟹ ¬ Q) ⟺ (P ⟹ ¬ Q);
	apply iff_intro;
	- if nnimp: ¬ ¬ (P ⟹ ¬ Q), P: P then ¬ Q;
		by nnimp_imp_nnot[OF nnimp P, unfold nnnot_iff].
	by nnot_intro.

lemma not_false_iff#simp ¬ false ⟺ true;
	by not_false.

lemma not_true_iff#simp ¬ true ⟺ false;
	unfold not_iff_imp_false.

---
## Negation and Conjunction
---

lemma nand_intro1: if nP: ¬ P then ¬ (P ∧ Q);
	by not_intro not_imp_false[OF nP].

lemma nand_intro2: if nQ: ¬ Q then ¬ (P ∧ Q);
	by not_intro not_imp_false[OF nQ].

lemma nand_iff_imp_not: ¬ (P ∧ Q) ⟺ (P ⟹ ¬ Q);
	simp not_iff_imp_false.

note imp_not_iff_nand: nand_iff_imp_not[dual].

lemma non_contradiction: ¬ (P ∧ ¬ P);
	unfold nand_iff_imp_not;
	by nnot_intro.

lemma false_nand: ¬ (false ∧ P);
	simp not_iff_imp_false.

lemma nand_false: ¬ (P ∧ false);
	simp not_iff_imp_false.
	
lemma nand_nnot_iff: ¬ (P ∧ ¬ ¬ Q) ⟺ ¬ (P ∧ Q);
	unfold+ nand_iff_imp_not nnnot_iff.

lemma nnot_nand_iff: ¬ (¬ ¬ P ∧ Q) ⟺ ¬ (P ∧ Q);
	unfold and.commute;
	unfold nand_nnot_iff;
	unfold and.commute.

lemma nnand_iff: ¬ ¬ (P ∧ Q) ⟺ ¬ ¬ P ∧ ¬ ¬ Q;
	apply iff_intro;
	- if nnand;
		apply+ and_intro nnand[THEN not_imp_imp_not];
		by #intro? nand_intro1 nand_intro2.
	fold nnot_nand_iff;
	by #simp imp_and_iff1.

lemma not_nniff_not: ¬ ¬ (¬ P ⟺ ¬ Q) ⟺ (¬ P ⟺ ¬ Q);
	unfold[at 0] iff_iff_and;
	unfold nnand_iff;
	unfold nnimp_not_iff;
	fold iff_iff_and.

---
## Disjunction Introduction
---

lemma or_iff_true1#simp if ! P then P ∨ Q ⟺ true;
	by iff_intro or_intro1.

lemma or_iff_true2#simp if ! Q then P ∨ Q ⟺ true;
	by iff_intro or_intro2.

lemma or_intro: if assm: ∀R. (P ⟹ R) ⟹ (Q ⟹ R) ⟹ R then P ∨ Q;
	apply assm;.

interpret or: iff.MetaAbsorb (∨) true;
	- by iff_intro.
	- by iff_intro.
	.

note#simp or.left_absorb or.right_absorb.

---
## Existence Introduction
---
lemma ex_intro: if assm: ∀Q. (∀x. P.[x] ⟹ Q) ⟹ Q then ∃x. P.[x];
	apply assm;
	- for x;
		by ex_intro1[of x].
	.

lemma ex_iff_true: for x if Px: P.[x] then (∃y. P.[y]) ⟺ true;
	apply iff_true;
	apply ex_intro1[OF Px].

---
## Double negation and universal quantification.

The following direction is provable in general, but the opposite direction requires something similar to the axiom of choice.
---
lemma nnall_imp: if nnall: ¬ ¬ (∀x. P.[x]) for x then ¬ ¬ P.[x];
	-> if nPx: ¬ P.[x];
		by not_imp_false[OF nnall] not_imp_not_all[OF nPx].
	.

---
The other direction is provable if inside the quantification has negation.
---
lemma nnall_not_iff: ¬ ¬ (∀x. ¬ P.[x]) ⟺ (∀x. ¬ P.[x]);
	apply iff_intro;
	- if 1;
		by 1[THEN nnall_imp, unfold nnnot_iff].
	by nnot_intro.

---
## Theories
---

extend MetaRelation begin

	extend AllRel begin

		lemma all_and_distrib: (∀x ⊏ a. P.[x] ∧ Q.[x]) ⟺ (∀x ⊏ a. P.[x]) ∧ (∀x ⊏ a. Q.[x]);
			simp all_iff all_and_distrib imp_and_distrib.

		lemma not_imp_not_all: if nP: ¬ P.[x], x: x ⊏ a then ¬ (∀y ⊏ a. P.[y]);
			-> if all;
				use nP all_elim1[OF all x].
			.
		lemma nnall_imp: if nnall: ¬ ¬ (∀x ⊏ a. P.[x]) then ∀x ⊏ a. ¬ ¬ P.[x];
			apply all_intro;
			-> if x: x ⊏ a, nPx: ¬ P.[x];
				by not_imp_false[OF nnall] not_imp_not_all[OF nPx] x.
			.
		lemma nnall_not_iff: ¬ ¬ (∀x ⊏ a. ¬ P.[x]) ⟺ (∀x ⊏ a. ¬ P.[x]);
			apply iff_intro;
			- if 1;
				by #cong all_cong_weak #intro 1[THEN nnall_imp, unfold nnnot_iff].
			by nnot_intro.

		lemma all_true: ∀x ⊏ a. true;
			simp all_iff.

	end

	theory ExRel :=
		fix (∃⊏).
		assume ex_def: (∃x ⊏ a. P.[x]) ⟺ (∃x. x ⊏ a ∧ P.[x]).
	begin
		lemma ex_intro1: if x: x ⊏ a, Px: P.[x] then ∃x ⊏ a. P.[x];
			unfold ex_def;
			by ex_intro1[of x] x Px.
		lemma ex_intro: if assm: ∀Q. (∀x. x ⊏ A ⟹ P.[x] ⟹ Q) ⟹ Q then ∃x ⊏ A. P.[x];
			apply assm;
			- for x;
				by ex_intro1[of x].
			.
	end

end

theory MetaIrreflexive (⊏) :=
	assume irrefl: ¬ x ⊏ x.
end

theory MetaAsymmetric (⊏) :=
	assume asym: x ⊏ y ⟹ ¬ y ⊏ x.
end
---
Note that antisymmetry is not yet definable, because it requires equality.
---
theory MetaOrder :=
	import MetaIrreflexive.
	import MetaTransitive.
begin
	interpret MetaAsymmetric;
		-> for x y if xy: x ⊏ y, yx: y ⊏ x then false;
			have xx: x ⊏ x;
				by trans[OF xy yx].
			by not_imp_false[OF irrefl xx].
		.
end

theory Membership :=
	import Std.Membership.
	interpret in: TypeSafeMinimal.MetaRelation (∈).
	fix (∀∈) (∃∈).
	import in: in.AllRel (∀∈).
	import in: in.ExRel (∃∈).
begin

	note#intro in.all_intro.
	note#elim in.all_elim.
	note#rule in.all_iff in.all_imp.
	note#simp in.all_true[THEN iff_true].

	extend CollectRel begin
		lemma Collect_iff: x ∈ {x ⊏ a. P.[x]} ⟺ x ⊏ a ∧ P.[x];
			by iff_intro Collect_intro #elim Collect_elim.
	end

end

theory ChoiceOp :=
	fix (such).
	assume such_intro: (∃x. P.[x]) ⟹ P.[such x. P.[x]].
end
