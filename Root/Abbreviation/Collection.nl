---
# Collection

We assume comprehensions `{x. P.[x]}` and they are identified by the membership.
---
import Minimal.Collection.
begin

interpret .Collect.

lemma bigcup_empty(simp) ⋃{} = {};
	simp bigcup_def empty_def Collect_eq_iff.

lemma bigcap_empty(simp) ⋂{} = UNIV;
	simp bigcap_def empty_def Collect_eq_iff UNIV_def.

---
## Binary Union
---
obtain (∪) where cup_def: X ∪ Y = {x. x ∈ X ∨ x ∈ Y};
	- for thesis if assm;
		apply abbrev2[of (p. {x. x ∈ fst p ∨ x ∈ snd p})];
		- for f if f;
			by assm[of f] #unfold f.
		.
	.
lemma in_cup_iff: x ∈ X ∪ Y ⟺ x ∈ X ∨ x ∈ Y;
	by #unfold cup_def in_Collect_iff.

interpret cup: eq.MetaAssociative (∪);
	by #unfold cup_def in_Collect_iff iff.or.assoc.

interpret cup: eq.MetaCommAbsorb (∪) UNIV;
	-; simp UNIV_def cup_def in_Collect_iff.
	-; by iff_intro or_intro or_elim(elim) #unfold cup_def Collect_eq_iff.
	.

note(simp) cup.left_absorb cup.right_absorb.

---
Within `COLLECT`, `(∪)` satisfies better algebraic properties.
---
namespace COLLECT:
	interpret cup: COLLECT.CommMonoidAbsorb (∪) UNIV {};
		-; by Collect_in_COLLECT #unfold cup_def.
		-; by COLLECT.empty.closed.
		- for X if X: X ∈ COLLECT then {} ∪ X = X;
			apply COLLECT_elim[OF X];
			- for P if (simp);
				simp cup_def in_Collect_iff in_empty_iff.
			.
		-; by cup.commute.
		-; by cup.assoc.
		-; by COLLECT.UNIV.closed.
		.
	interpret cup: Idempotent COLLECT (∪);
		by #unfold cup_def iff.or.idem Collect_in_eq.
end

obtain (∩) where cap_def: X ∩ Y = {x. x ∈ X ∧ x ∈ Y};
	- for thesis if assm;
		apply abbrev2[of (p. {x. x ∈ fst p ∧ x ∈ snd p})];
		- for f if f;
			by assm[of f] #unfold f.
		.
	.
lemma in_cap_iff: x ∈ X ∩ Y ⟺ x ∈ X ∧ x ∈ Y;
	by #unfold cap_def in_Collect_iff.

lemma Collect_in_cap(simp) {x. P.[x]} ∩ {x. Q.[x]} = {x. P.[x] ∧ Q.[x]};
	by #unfold cap_def in_Collect_iff.

interpret COLLECT.cap: Idempotent COLLECT (∩);
	by #unfold cap_def iff.and.idem Collect_in_eq.

lemma subseteq_cap_iff: X ⊆ Y ∩ Z ⟺ X ⊆ Y ∧ X ⊆ Z;
	simp subseteq_iff in_cap_iff imp_and_distrib all_and_distrib.

obtain (`) where image_def: f ` X = {y. ∃x ∈ X. y = f x};
	- for thesis if assm;
		apply abbrev2[of (p. {y. ∃x ∈ snd p. y = fst p x})];
		- for f if f;
			by assm[of f] #unfold f.
		.
	.
lemma in_image_iff: x ∈ f ` A ⟺ (∃a ∈ A. x = f a);
	unfold image_def in_Collect_iff.

lemma allIn_image_iff: (∀x ∈ f ` A. P.[x]) ⟺ (∀a ∈ A. P.[f a]);
	simp image_def;
	unfold allIn_iff;
	apply iff_intro;
	- if l: ∀x a. a ∈ A ⟹ x = f a ⟹ P.[x] for a if a: a ∈ A then P.[f a];
		apply l[OF a];.
	- if r: ∀x. x ∈ A ⟹ P.[f x] for x a if a: a ∈ A, x: x = f a then P.[x];
		note(cong) eq.cong_meta.
		unfold x;
		by r a.
	.

lemma image_subseteq_iff: f ` A ⊆ B ⟺ (∀a ∈ A. f a ∈ B);
	simp subseteq_iff_allIn allIn_image_iff.

lemma image_subseteq_elim1: if f: f ` A ⊆ B, aA: a ∈ A then f a ∈ B;
	by f[unfolded image_subseteq_iff, THEN allIn_elim1, OF aA].

lemma in_image: if x: x ∈ X then f x ∈ f ` X;
	by exIn_intro1[OF x] #unfold in_image_iff.

lemma image_mono: if AB: A ⊆ B then f ` A ⊆ f ` B;
	unfold image_subseteq_iff allIn_iff;
	- if a: a ∈ A then f a ∈ f ` B;
		apply in_image;
		apply subseteq_elim1[OF AB] a.
	.

syntax {_ ∈ _. _} := Collect.∈.
obtain Collect.∈ where CollectIn_def: {x ∈ X. P.[x]} = {x. x ∈ X ∧ P.[x]};
	- for thesis if assm;
		apply abbrev2[of (p. fst p ∩ Collect (snd p))];
		- for f if f;
			apply assm[of f];
			by #unfold f cap_def in_Collect_iff.
		.
	.

lemma in_CollectIn_iff: x ∈ {x ∈ A. P.[x]} ⟺ x ∈ A ∧ P.[x];
	simp CollectIn_def in_Collect_iff;.

lemma CollectIn_cong(cong)
	if X: X = X', P: ∀x. x ∈ X' ⟹ P.[x] ⟺ P'.[x] then {x ∈ X. P.[x]} = {x ∈ X'. P'.[x]};
	by #unfold X P CollectIn_def #cong iff.and_cong1.

lemma allIn_CollectIn_iff(simp)
	(∀x ∈ {x ∈ X. P.[x]}. Q.[x]) ⟺ (∀x. x ∈ X ⟹ P.[x] ⟹ Q.[x]);
	simp allIn_iff in_CollectIn_iff.

lemma CollectIn_subseteq(simp)
	{x ∈ X. P.[x]} ⊆ A ⟺ (∀x. x ∈ X ⟹ P.[x] ⟹ x ∈ A);
	simp subseteq_iff_allIn.

lemma subseteq_CollectIn(simp)
	A ⊆ {x ∈ X. P.[x]} ⟺ A ⊆ X ∧ (∀x ∈ A. P.[x]);
	simp subseteq_iff_allIn in_CollectIn_iff allIn_and_distrib.

lemma CollectIn_Collect(simp)
	{x ∈ {x. P.[x]}. Q.[x]} = {x. P.[x] ∧ Q.[x]};
	simp CollectIn_def in_Collect_iff.

lemma CollectIn_cap:
	{x ∈ A. P.[x]} ∩ {x ∈ B. Q.[x]} = {x ∈ A ∩ B. P.[x] ∧ Q.[x]};
	by iff_intro #unfold cap_def in_CollectIn_iff Collect_eq_iff.

lemma CollectIn_cap_Collect(simp)
	{x ∈ A. P.[x]} ∩ {x. Q.[x]} = {x ∈ A. P.[x] ∧ Q.[x]};
	simp CollectIn_def iff.and.assoc.

lemma Collect_cap_CollectIn(simp)
	{x. P.[x]} ∩ {x ∈ A. Q.[x]} = {x ∈ A. P.[x] ∧ Q.[x]};
	by Collect_ext iff_intro #unfold CollectIn_def iff.and.assoc.

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

lemma CollectSub_cong(cong)
	if A: A = A', P: ∀X. X ⊆ A' ⟹ P.[X] ⟺ P'.[X] then {X ⊆ A. P.[X]} = {X ⊆ A'. P'.[X]};
	note(cong) iff.and_cong1.
	simp CollectSub_def A P.

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
	- then true ∈ Decided;
		by #unfold in_Decided_iff.
	- then false ∈ Decided;
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
	- then P ∈ Decided ⟹ (¬ P) ∈ Decided;
		by or_intro nnot_intro #elim or_elim #unfold in_Decided_iff.
	- then P ∈ Decided ⟹ P ∨ ¬ P;
		unfold in_Decided_iff.
	.
end

lemma nnot_Decided: ¬ ¬ x ∈ Decided;
	unfold in_Decided_iff;
	by nnot_excluded_middle.
