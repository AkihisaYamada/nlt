---
# Naive Class Theory
---
import Abbreviation.
import Collect.
assume Collect_ext(cong) (∀x. P.[x] ⟺ Q.[x]) ⟹ {x. P.[x]} = {x. Q.[x]}.

begin

lemma Collect_eq_iff: {x. P.[x]} = {x. Q.[x]} ⟺ (∀x. P.[x] ⟺ Q.[x]);
	apply iff_intro;
	- if eq;
		fold in_Collect_iff;
		unfold eq.
	apply Collect_ext>0.

lemma bigcup_empty(simp) ⋃{} = {};
	simp bigcup_def Empty_def Collect_eq_iff.

lemma bigcap_empty(simp) ⋂{} = UNIV;
	simp bigcap_def Empty_def Collect_eq_iff UNIV_def.

obtain (∪) where cup_def: X ∪ Y = {x. x ∈ X ∨ x ∈ Y};
	- for thesis if assm;
		apply abbrev2[of (p. {x. x ∈ fst p ∨ x ∈ snd p})];
		- for f if f;
			by assm[of f] #unfold f.
		.
	.
lemma in_cup_iff: x ∈ X ∪ Y ⟺ x ∈ X ∨ x ∈ Y;
	by #unfold cup_def in_Collect_iff.

obtain (∩) where cap_def: X ∩ Y = {x. x ∈ X ∧ x ∈ Y};
	- for thesis if assm;
		apply abbrev2[of (p. {x. x ∈ fst p ∧ x ∈ snd p})];
		- for f if f;
			by assm[of f] #unfold f.
		.
	.
lemma in_cap_iff: x ∈ X ∩ Y ⟺ x ∈ X ∧ x ∈ Y;
	by #unfold cap_def in_Collect_iff.

obtain (`) where image_def: f ` X = {y. ∃x ∈ X. y = f x};
	- for thesis if assm;
		apply abbrev2[of (p. {y. ∃x ∈ snd p. y = fst p x})];
		- for f if f;
			by assm[of f] #unfold f.
		.
	.
lemma in_image_iff: x ∈ f ` A ⟺ (∃a ∈ A. x = f a);
	unfold image_def in_Collect_iff.
lemma in_image: if x: x ∈ X then f x ∈ f ` X;
	by exIn_intro1[OF x] #unfold in_image_iff.

syntax {_ ∈ _. _} := Collect.∈.
obtain Collect.∈ where CollectIn_def: {x ∈ X. P.[x]} = {x. x ∈ X ∧ P.[x]};
	- for thesis if assm;
		apply abbrev2[of (p. fst p ∩ Collect (snd p))];
		- for f if f;
			apply assm[of f];
			by #unfold f cap_def in_Collect_iff.
		.
	.
lemma CollectIn_cong:
	if X: X = X', P: ∀x. x ∈ X' ⟹ P.[x] ⟺ P'.[x] then {x ∈ X. P.[x]} = {x ∈ X'. P'.[x]};
	by #unfold X P CollectIn_def #cong iff.and_cong1.

lemma allIn_CollectIn_iff(simp)
	(∀x ∈ {x ∈ X. P.[x]}. Q.[x]) ⟺ (∀x. x ∈ X ⟹ P.[x] ⟹ Q.[x]);
	simp allIn_iff CollectIn_def in_Collect_iff.

syntax {_ ⊆ _. _} := Collect.⊆.
obtain Collect.⊆ where CollectSub_def: {X ⊆ A. P.[X]} = {X. X ⊆ A ∧ P.[X]};
	- for thesis if assm;
		apply abbrev2[of (p. Collect.∈ (Pow (fst p)) (snd p))];
		- for f if f;
			apply assm[of f];
			by #unfold f CollectIn_def.
		.
	.

lemma in_CollectSub_iff: X ∈ {X ⊆ A. P.[X]} ⟺ X ⊆ A ∧ P.[X];
	simp CollectSub_def in_Collect_iff.

lemma allIn_CollectSub_iff(simp) (∀X ∈ {X ⊆ A. P.[X]}. Q.[X]) ⟺ (∀X. X ⊆ A ⟹ P.[X] ⟹ Q.[X]);
	simp allIn_iff in_Collect_iff in_CollectSub_iff allSub_iff.

obtain class where class_def: class A (⊑) x = {y ∈ A. x ⊑ y};
	- for thesis if assm;
		apply abbrev3[of (p. {y ∈ fst p. fst (snd p) (snd (snd p)) y})];
		- for f if f;
			by assm[of f] #unfold f CollectIn_def.
		.
	.
infix // 110 111 110.
obtain (//) where quotient_def: A // (⊑) = {C. ∃x ∈ A. C = {y ∈ A. x ⊑ y}};
	- for thesis if assm;
		apply abbrev2[of (p. {C. ∃x ∈ fst p. C = {y ∈ fst p. snd p x y}})];
		- for f if f;
			by assm[of f] #unfold f CollectIn_def.
		.
	.
obtain (→) where fun_def: A → B = {f. ∀x ∈ A. f x ∈ B};
	- for thesis if assm;
		apply abbrev2[of (p. {f. ∀x ∈ fst p. f x ∈ snd p})];
		- for f if f;
			by assm[of f] #unfold f.
		.
	.
interpret Fun;
	by #unfold fun_def in_Collect_iff allIn_iff.

lemma in_fun_intro: if f: ∀x. x ∈ A ⟹ f x ∈ B then f ∈ A → B;
	by f allIn_intro #unfold fun_def in_Collect_iff.

---
## The Classical Propositional Logic

The class of *decided* terms form classical propositional logic.
---

obtain Decided where Decided_def: Decided = {x. x ∨ ¬x};
	- for thesis if assm;
		apply assm[OF eq.refl].
	.

lemma in_Decided_iff: P ∈ Decided ⟺ P ∨ ¬P;
	unfold Decided_def in_Collect_iff.

lemma in_Decided_cong: if P: P ⟺ P' then P ∈ Decided ⟺ P' ∈ Decided;
	unfold in_Decided_iff P.

namespace Decided:
interpret Classical;
	instantiate Prop := Decided.
	note! not_intro and_intro iff_intro.
	note(elim) and_elim iff_elim false_elim.
	note(intro 1) not_elim.
	note(cong) in_Decided_cong.
	interpret imp: Magma Decided (⟹);
		- for P Q if P: P ∈ Decided, Q: Q ∈ Decided then (P ⟹ Q) ∈ Decided;
			unfold in_Decided_iff;
			apply or_elim[OF P[unfolded in_Decided_iff]];
			- if P: P;
				by Q[unfolded in_Decided_iff] #unfold imp_imp_iff[OF P].
			-; by or_intro1.
			.
		.
	interpret and: Magma Decided (∧);
		- for P Q if P: P ∈ Decided, Q: Q ∈ Decided then (P ∧ Q) ∈ Decided;
			apply P[unfolded in_Decided_iff, THEN or_elim];
			- if P1: P;
				unfold in_Decided_iff;
				apply Q[unfolded in_Decided_iff, THEN or_elim];
				- if Q1: Q; by or_intro1 P1 Q1.
				- if Q0: ¬Q; by or_intro2 nand_intro2[OF Q0].
				.
			- if P0: ¬P;
				by in_fun_intro or_intro2 nand_intro1[OF P0] #unfold in_Decided_iff.
			.
		.
	- true ∈ Decided;
		by #unfold in_Decided_iff.
	- false ∈ Decided;
		by #unfold in_Decided_iff.
	- for P Q if ! P ∈ Decided, ! Q ∈ Decided then (P ⟺ Q) ∈ Decided;
		by in_fun_intro and.closed imp.closed #unfold iff_iff_and.
	- for P Q if P: P ∈ Decided, Q: Q ∈ Decided then (P ∨ Q) ∈ Decided;
		apply P[unfolded in_Decided_iff, THEN or_elim];
		- if P1: P;
			by in_fun_intro #unfold in_Decided_iff iff_true[OF P1].
		- if P0: ¬P;
			apply Q[unfolded in_Decided_iff, THEN or_elim];
			- if Q1: Q;
				by #unfold in_Decided_iff iff_true[OF Q1].
			- if Q0: ¬Q;
				by or_intro2 P0 Q0 #unfold in_Decided_iff nor_iff.
			.
		.
	- P ∈ Decided ⟹ (¬ P) ∈ Decided;
		by or_intro nnot_intro #elim or_elim #unfold in_Decided_iff.
	- P ∈ Decided ⟹ P ∨ ¬ P;
		unfold in_Decided_iff.
	.
end

lemma nnot_Decided: ¬ ¬ x ∈ Decided;
	unfold in_Decided_iff;
	by nnot_excluded_middle.

---
## Fixed Points
---
print.
obtain extreme_bounds where extreme_bounds_def: extreme_bounds A (≤) X = {s. extreme_bound A (≤) X s};
	- for thesis if assm;
		apply abbrev3[of (p. {s. extreme_bound (fst p) (fst (snd p)) (snd (snd p)) s})];
		- for f if (simp);
			apply assm[of f];
			.
		.
	.
lemma in_extreme_bounds_iff: s ∈ extreme_bounds A (≤) X ⟺ extreme_bound A (≤) X s;
	simp extreme_bounds_def in_Collect_iff.

lemma extreme_bounds_subseteq_carrier: extreme_bounds A (≤) X ⊆ A;
	apply subseteq_intro;
	simp extreme_bounds_def in_Collect_iff extreme_bound_iff extreme_iff.

theory Monotone:
	fix A (≤) f.
	assume range: f ` A ⊆ A.
	assume mono: monotone A (≤) (≤) f.
begin
	obtain Complete where
		Complete_def: Complete = {X ⊆ A. f ` X ⊆ X ∧ (∀Y ⊆ X. extreme_bounds A (≤) Y ⊆ X)};
		- for thesis if assm;
			apply assm[OF eq.refl].
		.
	lemma Complete_carrier: X ∈ Complete ⟹ X ⊆ A;
		simp Complete_def in_CollectSub_iff.
	lemma Complete_closed: X ∈ Complete ⟹ f ` X ⊆ X;
		simp Complete_def in_CollectSub_iff.
	lemma Complete_complete: X ∈ Complete ⟹ ∀Y ⊆ X. extreme_bounds A (≤) Y ⊆ X;
		simp Complete_def in_CollectSub_iff.

	lemma domain_in_Complete: A ∈ Complete;
		simp Complete_def in_CollectSub_iff iff_true[OF range] iff_true[OF extreme_bounds_subseteq_carrier];.
		
	lemma core_in_Complete: ⋂Complete ∈ Complete;
		unfold[on (=), at 1] Complete_def;
		unfold in_CollectSub_iff;
		apply+ and_intro allSub_intro subseteq_intro;
		- for x if x: x ∈ ⋂Complete;
			apply in_bigcap_elim1[OF x domain_in_Complete].
		simp in_image_iff allIn_iff subseteq_iff;
		- for y x if x: x ∈ ⋂Complete, y: y = f x then y ∈ ⋂Complete;
			apply in_bigcap_intro;
			- if X: X ∈ Complete then y ∈ X;
				have xX: x ∈ X;
					by in_bigcap_elim1[OF x] X.
				apply Complete_closed[OF X, THEN subseteq_elim1];
				unfold y;
				by in_image xX.
			.
		- for X if X: X ⊆ ⋂ Complete then extreme_bounds A (≤) X ⊆ ⋂ Complete;
			unfold subseteq_bigcap_iff;
			apply allIn_intro;
			- for Y if Y: Y ∈ Complete then extreme_bounds A (≤) X ⊆ Y;
				apply Complete_complete[OF Y, THEN allSub_elim1];
				by X[unfolded subseteq_bigcap_iff, THEN allIn_elim1, OF Y].
			.
		.
end

