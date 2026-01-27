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

---
Let us call terms of form `{x. P.[x]}` *collections*.
---
obtain COLLECT where COLLECT_def: COLLECT = {C. ∃P. C = {x. P.[x]}};
	- for thesis if assm;
		apply assm[OF eq.refl].
	.
lemma in_COLLECT_iff_ex: X ∈ COLLECT ⟺ (∃P. X = {x. P.[x]});
	unfold COLLECT_def in_Collect_iff;.

lemma Collect_in_COLLECT: {x. P.[x]} ∈ COLLECT;
	unfold in_COLLECT_iff_ex;
	apply ex_intro;
	- for thesis if assm;
		apply assm[OF eq.refl].
	.

lemma COLLECT_elim: if A: A ∈ COLLECT, assm: ∀P. A = {x. P.[x]} ⟹ Q then Q;
	apply A[unfolded in_COLLECT_iff_ex, THEN ex_elim, OF assm].

lemma Collect_in_eq: if A: A ∈ COLLECT then {x. x ∈ A} = A;
	apply COLLECT_elim[OF A];
	- for P if (simp);
		simp in_Collect_iff.
	.

lemma COLLECT_eq_iff: if A: A ∈ COLLECT, B: B ∈ COLLECT then A = B ⟺ (∀x. x ∈ A ⟺ x ∈ B);
	apply COLLECT_elim[OF A];
	- for P if (simp);
		apply COLLECT_elim[OF B];
		- for Q if (simp);
			simp Collect_eq_iff in_Collect_iff.
		.
	.

---
The collections form a collection.
---
lemma COLLECT_COLLECT: COLLECT ∈ COLLECT;
	unfold[at 0 0 0] COLLECT_def;
	by Collect_in_COLLECT.

---
It is crucial that collections are not classes; membership is not decided.
---
lemma Russels_paradox_COLLECT: ∃X ∈ COLLECT. ∃x ∈ COLLECT. ¬(x ∈ X ∨ x ∉ X);
	obtain R where R_def: R = {X. X ∉ X};
		- for thesis if assm;
			apply assm[OF eq.refl].
		.
	have RC: R ∈ COLLECT;
		by Collect_in_COLLECT #unfold R_def.
	have iff: R ∈ R ⟺ R ∉ R;
		unfold[at 0 0 1] R_def;
		unfold in_Collect_iff.
	apply+ exIn_intro1[OF RC] not_intro;
	- if or: R ∈ R ∨ R ∉ R then false;
		apply or_elim[OF or];
		- if 1: R ∈ R;
			by not_imp_false[OF 1[unfolded iff, unfolded notIn_iff] 1].
		- if 0: R ∉ R;
			by not_imp_false[OF 0[unfolded notIn_iff] 0[folded iff]].
		.
	.

lemma bigcup_in_COLLECT: ⋃XX ∈ COLLECT;
	unfold bigcup_def;
	apply Collect_in_COLLECT.

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

---
## Fixed Points
---

obtain extreme_bound where
	extreme_bound_def: extreme_bound A (≤) X s ⟺ extreme {b ∈ A. bound X (≤) b} (dual (≤)) s;
	- for thesis if assm;
		apply abbrev4[of (p. extreme {b ∈ fst p. bound (fst (snd (snd p))) (fst (snd p)) b} (dual (fst (snd p))) (snd (snd (snd p))))];
		- for f if (simp);
			apply assm[of f];
			simp extreme_iff bound_iff allIn_Collect_iff in_Collect_iff; .
		.
	.

lemma extreme_bound_carrier: extreme_bound A (≤) X s ⟹ s ∈ A;
	simp extreme_bound_def extreme_iff in_CollectIn_iff.

lemma extreme_bound_imp_bound: extreme_bound A (≤) X s ⟹ bound X (≤) s;
	simp extreme_bound_def extreme_iff in_CollectIn_iff.

lemma extreme_bound_bound_imp: if sup: extreme_bound A (≤) X s, bA: b ∈ A, bound: bound X (≤) b then s ≤ b;
	have 1: b ∈ {b ∈ A. bound X (≤) b};
		by bound bA #unfold in_CollectIn_iff.
	note 2: sup[unfolded extreme_bound_def, THEN extreme_imp_bound, THEN bound_elim1, OF 1].
	by 2[simplified].

lemma extreme_bound_iff:
	extreme_bound A (≤) X s ⟺ s ∈ A ∧ bound X (≤) s ∧ (∀b ∈ A. bound X (≤) b ⟹ s ≤ b);
	by iff_intro #unfold extreme_bound_def extreme_iff bound_iff[of _ (dual (≤))] in_CollectIn_iff allIn_iff.

lemma extreme_bound_intro:
	if sA: s ∈ A, Xs: bound X (≤) s, sB: ∀b. b ∈ A ⟹ bound X (≤) b ⟹ s ≤ b then extreme_bound A (≤) X s;
	simp extreme_bound_iff;
	by sA Xs sB.

lemma extreme_bound_elim:
	if	s: extreme_bound A (≤) X s,
		assm: s ∈ A ⟹ bound X (≤) s ⟹ (∀b. b ∈ A ⟹ bound X (≤) b ⟹ s ≤ b) ⟹ P
	then P;
	use s[unfolded extreme_bound_iff allIn_iff];
	by assm.

lemma bound_bigcup: bound XX (⊆) (⋃XX);
	apply bound_intro;
	- if X: X ∈ XX then X ⊆ ⋃XX;
		apply subseteq_intro;
		- if x: x ∈ X;
			by in_bigcup_intro1[OF x X].
		.
	.

lemma UNIV_bigcup_extreme_bound: extreme_bound UNIV (⊆) XX (⋃XX);
	apply+ extreme_bound_intro in_UNIV bound_bigcup;
	unfold bigcup_subseteq_iff_bound.

lemma COLLECT_bigcup_extreme_bound: extreme_bound COLLECT (⊆) XX (⋃XX);
	apply extreme_bound_intro bigcup_in_COLLECT bound_bigcup;
	unfold bigcup_subseteq_iff_bound.

obtain extreme_bounds where extreme_bounds_def: extreme_bounds A (≤) X = {s. extreme_bound A (≤) X s};
	- for thesis if assm;
		apply abbrev3[of (p. {s. extreme_bound (fst p) (fst (snd p)) (snd (snd p)) s})];
		- for f if (simp);
			apply assm[of f].
		.
	.
lemma in_extreme_bounds_iff: s ∈ extreme_bounds A (≤) X ⟺ extreme_bound A (≤) X s;
	simp extreme_bounds_def in_Collect_iff.

lemma extreme_bounds_carrier: extreme_bounds A (≤) X ⊆ A;
	apply subseteq_intro;
	simp extreme_bounds_def in_Collect_iff in_CollectIn_iff extreme_bound_iff extreme_iff.

lemma bound_extreme_bounds: if bA: b ∈ A, Xb: bound X (≤) b then bound (extreme_bounds A (≤) X) (≤) b;
	apply bound_intro;
	unfold in_extreme_bounds_iff;
	- if s: extreme_bound A (≤) X s then s ≤ b;
		by extreme_bound_bound_imp[OF s bA Xb].
	.

obtain complete where
	complete_iff: complete C A (≤) ⟺ (∀X ⊆ A. C X (≤) ⟹ ∃s. extreme_bound A (≤) X s);
	- for thesis if assm;
		apply abbrev3[of (p. (∀X ⊆ fst (snd p). fst p X (snd (snd p)) ⟹ ∃s. extreme_bound (fst (snd p)) (snd (snd p)) X s))];
		- for f if (simp);
			apply assm[of f].
		.
	.

theory FixedPoint:
	fix A (≤) f.
	assume closed: f ` A ⊆ A.
begin

	obtain PreFixed where PreFixed_def: PreFixed = {x ∈ A. f x ≤ x};
		- for thesis if assm;
			by assm[OF eq.refl].
		.
	obtain PostFixed where PostFixed_def: PostFixed = {x ∈ A. x ≤ f x};
		- for thesis if assm;
			by assm[OF eq.refl].
		.
	obtain QuasiFixed where QuasiFixed_def: QuasiFixed = {x ∈ A. sym (≤) (f x) x};
		- for thesis if assm;
			by assm[OF eq.refl].
		.
	lemma QuasiFixed_eq_Pre_Post: QuasiFixed = PreFixed ∩ PostFixed;
		by Collect_ext iff_intro #unfold sym_iff QuasiFixed_def PreFixed_def PostFixed_def CollectIn_def.

	obtain Complete where
		Complete_def: Complete = {X ⊆ A. f ` X ⊆ X ∧ (∀Y ⊆ X. extreme_bounds A (≤) Y ⊆ X)};
		- for thesis if assm;
			by assm[OF eq.refl].
		.
	lemma Complete_imp_carrier: X ∈ Complete ⟹ X ⊆ A;
		simp Complete_def in_CollectSub_iff.
	lemma Complete_imp_closed: X ∈ Complete ⟹ f ` X ⊆ X;
		simp Complete_def in_CollectSub_iff.
	lemma Complete_imp_complete: X ∈ Complete ⟹ ∀Y ⊆ X. extreme_bounds A (≤) Y ⊆ X;
		simp Complete_def in_CollectSub_iff.
	lemma Complete_imp_extreme_bounds: if X: X ∈ Complete, YX: Y ⊆ X then extreme_bounds A (≤) Y ⊆ X;
		by Complete_imp_complete[OF X, THEN allSub_elim1, OF YX].

	lemma carrier_in_Complete: A ∈ Complete;
		simp Complete_def in_CollectSub_iff iff_true[OF closed] iff_true[OF extreme_bounds_carrier];.

	obtain Core where Core_def: Core = ⋂Complete;
		- for thesis if assm;
			by assm[OF eq.refl].
		.

	lemma Core_carrier: Core ⊆ A;
		apply subseteq_intro;
		- for x if x: x ∈ Core;
			apply in_bigcap_elim1[OF x[unfolded Core_def] carrier_in_Complete].
		.

	lemma Core_closed: f ` Core ⊆ Core;
		simp in_image_iff allIn_iff subseteq_iff_allIn;
		- for y x if x: x ∈ Core, y: y = f x then y ∈ Core;
			unfold Core_def;
			apply in_bigcap_intro;
			- if X: X ∈ Complete then y ∈ X;
				have xX: x ∈ X;
					by in_bigcap_elim1[OF x[unfolded Core_def]] X.
				apply Complete_imp_closed[OF X, THEN subseteq_elim1];
				unfold y;
				by in_image xX.
			.
		.

	lemma Core_complete: if X: X ⊆ Core then extreme_bounds A (≤) X ⊆ Core;
		unfold Core_def subseteq_bigcap_iff;
		- for Y if Y: Y ∈ Complete then extreme_bounds A (≤) X ⊆ Y;
			apply Complete_imp_complete[OF Y, THEN allSub_elim1];
			by X[unfolded Core_def subseteq_bigcap_iff, OF Y].
		.

	lemma Core_in_Complete: Core ∈ Complete;
		unfold[on (=), at 1] Complete_def;
		unfold in_CollectSub_iff;
		by and_intro allSub_intro Core_carrier Core_closed Core_complete.

	obtain SupCore where SupCore_def: SupCore = extreme_bounds A (≤) Core;
		- for thesis if assm;
			by assm[OF eq.refl].
		.

	lemma SupCore_Core: SupCore ⊆ Core;
		simp SupCore_def;
		apply Complete_imp_extreme_bounds[OF Core_in_Complete].

	lemma image_SupCore_Core: f ` SupCore ⊆ Core;
		have 1: f ` SupCore ⊆ f ` Core;
			apply image_mono SupCore_Core.
		apply subseteq.trans[OF 1];
		apply Complete_imp_closed[OF Core_in_Complete].

	lemma pre_fp: if p: extreme_bound A (≤) Core p then f p ≤ p;
		have pFP: p ∈ SupCore;
			simp SupCore_def in_extreme_bounds_iff;
			by p.
		have fpC: f p ∈ Core;
			by image_SupCore_Core[unfolded image_subseteq_iff allIn_iff, OF pFP].
		by extreme_bound_imp_bound[OF p, THEN bound_elim1, OF fpC].

	lemma SupCore_PreFixed: SupCore ⊆ PreFixed;
		simp PreFixed_def SupCore_def;
		by extreme_bounds_carrier pre_fp #unfold in_extreme_bounds_iff.

	lemma monotone_SupCore_PostFixed: if mono: monotone A (≤) (≤) f then SupCore ⊆ PostFixed;
		simp subseteq_iff in_extreme_bounds_iff PostFixed_def in_CollectIn_iff;
		- if pS: p ∈ SupCore then p ∈ A ∧ p ≤ f p;
			have p: extreme_bound A (≤) Core p;
				use pS;
				by #unfold SupCore_def in_Collect_iff in_extreme_bounds_iff.
			apply and_intro;
			show pA: p ∈ A;
				by extreme_bound_carrier[OF p].
			have fpA: f p ∈ A;
				by image_subseteq_elim1[OF closed] pA.
			have pC: p ∈ Core;
				by SupCore_Core[THEN subseteq_elim1, OF pS].
			obtain D where D_def: D = {d ∈ Core. d ≤ f p};
				- for thesis if assm;
					apply assm[OF eq.refl].
				.
			have DC: D ⊆ Core;
				simp D_def.
			have D: D ∈ Complete;
				unfold Complete_def in_CollectSub_iff;
				apply+ and_intro allSub_intro;
				- then D ⊆ A;
					simp D_def;
					by Core_carrier[THEN subseteq_elim1].
				- then f ` D ⊆ D;
					simp D_def image_subseteq_iff in_CollectIn_iff;
					- for x if xC: x ∈ Core, xfp: x ≤ f p then f x ∈ Core ∧ f x ≤ f p;
						apply and_intro;
						- then f x ∈ Core;
							apply Core_closed[THEN subseteq_elim1];
							by in_image xC.
						- then f x ≤ f p;
							apply monotone_elim1[OF mono];
							- then x ∈ A;
								apply Core_carrier[THEN subseteq_elim1, OF xC].
							- then p ∈ A;
								apply extreme_bound_carrier[OF p].
							- then x ≤ p;
								apply extreme_bound_imp_bound[OF p, THEN bound_elim1] xC.
							.
						.
					.
				- if XD: X ⊆ D then extreme_bounds A (≤) X ⊆ D;
					simp D_def;
					apply and_intro;
					- then extreme_bounds A (≤) X ⊆ Core;
						have XC: X ⊆ Core;
							by subseteq.trans[OF XD DC].
						by Core_complete[OF XC].
					simp extreme_bounds_def;
					- if x: extreme_bound A (≤) X x then x ≤ f p;
						apply extreme_bound_bound_imp[OF x fpA];
						use XD[unfolded D_def];
						simp bound_iff.
					.
				.
			have CD: Core ⊆ D;
				simp Core_def subseteq_iff;
				- if x: x ∈ ⋂Complete then x ∈ D;
					by x[unfolded in_bigcap_iff, OF D].
				.
			have pD: p ∈ D;
				by subseteq_elim1[OF CD pC].
			use pD[simplified D_def in_CollectIn_iff].
		.



	lemma monotone_SupCore_QuasiFixed: if mono: monotone A (≤) (≤) f then SupCore ⊆ QuasiFixed;
		unfold QuasiFixed_eq_Pre_Post subseteq_cap_iff;
		by SupCore_PreFixed monotone_SupCore_PostFixed[OF mono].

end

theory Complete:
	fix A (≤).
	assume ex_extreme_bound: if X ⊆ A then ∃s. extreme_bound A (≤) X s.
begin

	lemma monotone_imp_ex_qfp:
		if closed: f ` A ⊆ A, mono: monotone A (≤) (≤) f then ∃p ∈ A. sym (≤) (f p) p;
		interpret FixedPoint;
			by closed.
		obtain p where p: extreme_bound A (≤) Core p;
			apply ex_extreme_bound[OF Core_carrier, THEN ex_elim]=.
		apply exIn_intro1[of p];
		-; apply extreme_bound_carrier[OF p].
		have pS: p ∈ SupCore;
			by p #unfold SupCore_def in_Collect_iff in_extreme_bounds_iff.
		have pF: p ∈ QuasiFixed;
			by monotone_SupCore_QuasiFixed[OF mono, THEN subseteq_elim1, OF pS].
		use pF;
		simp QuasiFixed_def in_CollectIn_iff.

end

theory CompleteAntisymmetric:
	import Antisymmetric.
	import Complete.
begin
	lemma sym_imp_eq: if xy: sym (≤) x y, x: x ∈ A, y: y ∈ A then x = y;
		use xy;
		by antisym x y #unfold sym_iff.
	theorem monotone_imp_ex_fixed:
		if closed: f ` A ⊆ A, mono: monotone A (≤) (≤) f then ∃p ∈ A. f p = p;
		obtain p where pA: p ∈ A, sym: sym (≤) (f p) p;
			apply monotone_imp_ex_qfp[OF closed mono, THEN exIn_elim]=.
		apply exIn_intro1[OF pA];
		by sym_imp_eq[OF sym] pA image_subseteq_elim1[OF closed pA].
end

theory CompleteOrder:
	import Order.
	import Complete.
begin
	interpret CompleteAntisymmetric.
end

namespace COLLECT:

	interpret subseteq: CompleteOrder COLLECT (⊆);
		-; .
		- if xy: x ⊆ y, yz: y ⊆ z;
			by subseteq.trans[OF xy yz].
		- if XY: X ⊆ Y, YX: Y ⊆ X, X: X ∈ COLLECT, Y: Y ∈ COLLECT then X = Y;
			unfold COLLECT_eq_iff[OF X Y];
			- for x;
				apply iff_intro;
				-; by subseteq_elim1[OF XY].
				-; by subseteq_elim1[OF YX].
				.
			.
		- for XX if _;
			apply ex_intro1[of (⋃XX)];
			by COLLECT_bigcup_extreme_bound.
		.

end

thm COLLECT.subseteq.monotone_imp_ex_fixed.

