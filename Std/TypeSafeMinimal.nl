import Iff.
interpret True.

fix false (∧) (∨) (¬) (∃).

import And.

assume not_intro: if P ⟹ false then ¬P.
assume not_imp_false#intro?[after 1] if ¬P, P then false.


assume or_intro1: for P Q if P then P ∨ Q.
assume or_intro2: for P Q if Q then P ∨ Q.

assume ex_intro1: for x if P.[x] then ∃x. P.[x].

begin

---
## Negation
---

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
	by not_intro #elim PnQ.

-- utilizes shared false
lemma nimp_imp_not: if nimp: ¬(P ⟹ Q) then ¬Q;
	apply not_intro;
	by not_imp_false[OF nimp].

-- utilizes shared false
lemma nimp_not_imp_not: if nimpn: ¬(P ⟹ ¬Q) then ¬ ¬ P;
	apply not_intro;
	- if nP: ¬P then false;
		apply not_imp_false[OF nimpn];
		- if P: P then ¬Q;
			apply not_intro;
			by not_imp_false[OF nP P].
		.
	.


lemma nnot_intro: P ⟹ ¬ ¬ P;
	by not_intro.

lemma nnot_imp_imp: if imp: ¬ ¬ P ⟹ Q then P ⟹ Q;
	by imp nnot_intro.

lemma not_imp_not_all: ¬ P.[x] ⟹ ¬(∀y. P.[y]);
	by not_intro.

lemma nnot_imp_nnot: if nnP: ¬ ¬ P, PQ: P ⟹ Q then ¬ ¬ Q;
	apply not_intro;
	- if nQ: ¬Q;
		use nnP;
		by imp_not_imp[OF PQ nQ].
	.

lemma nnot_not_imp_nimp: if nnP: ¬ ¬ P, ! ¬Q then ¬(P ⟹ Q);
	apply not_intro;
	- if PQ: P ⟹ Q;
		by nnot_imp_nnot[OF nnP PQ].
	.

lemma nnimp_imp_nnot: if nnPQ: ¬ ¬ (P ⟹ Q), P: P then ¬ ¬ Q;
	apply not_intro;
	- if nQ: ¬Q;
		have nPQ: ¬(P ⟹ Q);
			apply not_intro;
			- if PQ: P ⟹ Q;
				by nQ PQ[OF P].
			.
		use nnPQ nPQ.
	.

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
		assume ex_iff: (∃x ⊏ a. P.[x]) ⟺ (∃x. x ⊏ a ∧ P.[x]).
	begin
		lemma ex_intro1: if x: x ⊏ a, Px: P.[x] then ∃x ⊏ a. P.[x];
			unfold ex_iff;
			by ex_intro1[of x] x Px.
		lemma ex_intro: if assm: ∀Q. (∀x. x ⊏ A ⟹ P.[x] ⟹ Q) ⟹ Q then ∃x ⊏ A. P.[x];
			apply assm;
			- for x;
				by ex_intro1[of x].
			.
	end

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
