---
# Set Comprehension

This theory assumes set comprehension `{x. P.[x]}`.
---
import Minimal.Collect.

begin

interpret .Membership.

lemma notIn_empty: x ∉ {};
	by #unfold empty_def notIn_iff in_Collect_iff const_eq.

---
## Set Theoretic Notations
---

interpret AllIn;
	obtain (∀∈) where allIn_iff: (∀x ∈ A. P.[x]) ⟺ (∀x. x ∈ A ⟹ P.[x]);
		- for thesis if assm;
			apply abbrev2[of (p. ∀x. x ∈ fst p ⟹ x ∈ Collect (snd p))];
			- for f if f;
				apply assm[of f];
				by #unfold f in_Collect_iff.
			.
		.
	.

lemma allIn_cong(cong)
	if A: A = A', P: ∀x. x ∈ A' ⟹ P.[x] ⟺ P'.[x] then (∀x ∈ A. P.[x]) ⟺ (∀x ∈ A'. P'.[x]);
	simp allIn_iff A P.

lemma allIn_Collect_iff(simp) (∀x ∈ {x. P.[x]}. Q.[x]) ⟺ (∀x. P.[x] ⟹ Q.[x]);
	simp allIn_iff in_Collect_iff.

lemma allIn_and_distrib: (∀x ∈ X. P.[x] ∧ Q.[x]) ⟺ (∀x ∈ X. P.[x]) ∧ (∀x ∈ X. Q.[x]);
	simp allIn_iff imp_and_distrib all_and_distrib.

interpret ExIn;
	obtain (∃∈) where exIn_iff: (∃x ∈ A. P.[x]) ⟺ (∃x. x ∈ A ∧ P.[x]);
		- for thesis if assm;
			apply abbrev2[of (p. ∃x. x ∈ fst p ∧ x ∈ Collect (snd p))];
			- for f if f;
				apply assm[of f];
				by #unfold f in_Collect_iff.
			.
		.
	.

lemma exlIn_cong(cong)
	if A: A = A', P: ∀x. x ∈ A' ⟹ P.[x] ⟺ P'.[x] then (∃x ∈ A. P.[x]) ⟺ (∃x ∈ A'. P'.[x]);
	note(cong) iff.and_cong1.
	simp exIn_iff A P.

lemma exIn_Collect_iff(simp) (∃x ∈ {x. P.[x]}. Q.[x]) ⟺ (∃x. P.[x] ∧ Q.[x]);
	simp exIn_iff in_Collect_iff.

lemma exIn_imp_iff_allIn(simp) ((∃x ∈ A. P.[x]) ⟹ Q) ⟺ (∀x ∈ A. P.[x] ⟹ Q);
	simp allIn_iff exIn_iff.

obtain (⊆) where subseteq_iff_allIn: X ⊆ Y ⟺ (∀x ∈ X. x ∈ Y);
	- for thesis if assm;
		apply abbrev2[of (p. ∀x ∈ fst p. x ∈ snd p)];
		- for f if f;
			by assm[of f] #unfold f.
		.
	.
note subseteq_iff: subseteq_iff_allIn[unfolded allIn_iff].
note subseteq_intro: subseteq_iff[THEN iff_elim2].
note subseteq_elim1: subseteq_iff[THEN iff_elim1].

interpret subseteq: Minimal.MetaPreorder (⊆);
	-; by subseteq_intro.
	- if XY: X ⊆ Y, YZ: Y ⊆ Z then X ⊆ Z;
		apply subseteq_intro;
		- if X: x ∈ X then x ∈ Z;
			note Y: subseteq_elim1[OF XY X].
			by subseteq_elim1[OF YZ Y].
		.
	.

note(simp) subseteq.refl_iff_true.

lemma subseteq_Collect_iff_allIn(simp) X ⊆ {x. P.[x]} ⟺ (∀x ∈ X. P.[x]);
	simp subseteq_iff_allIn in_Collect_iff.

obtain (∀⊆) where allSub_iff: (∀X ⊆ A. P.[X]) ⟺ (∀X. X ⊆ A ⟹ P.[X]);
	- for thesis if assm;
		apply abbrev2[of (p. ∀x. x ⊆ fst p ⟹ x ∈ Collect (snd p))];
		- for f if f;
			apply assm[of f];
			by #unfold f in_Collect_iff.
		.
	.

lemma allSub_cong(cong)
	if A: A = A', P: ∀X. X ⊆ A' ⟹ P.[X] ⟺ P'.[X] then (∀X ⊆ A. P.[X]) ⟺ (∀X ⊆ A'. P'.[X]);
	simp allSub_iff A P.

note allSub_intro: allSub_iff[THEN iff_elim2].

note allSub_elim1: allSub_iff[THEN iff_elim1].

lemma allSub_indep(simp) (∀X ⊆ A. P) ⟺ P;
	apply iff_intro;
	- if all;
		apply allSub_elim1[OF all subseteq.refl].
	by iff_intro allSub_intro.

---
## Notions for Order Theory
---

obtain bound where bound_iff: bound X (≤) b ⟺ (∀x ∈ X. x ≤ b);
	- for thesis if assm;
		apply abbrev3[of (p. ∀x ∈ fst p. fst (snd p) x (snd (snd p)))];
		- for f if (simp);
			apply assm[of f].
		.
	.

lemma bound_intro: if all: ∀x. x ∈ X ⟹ x ≤ b then bound X (≤) b;
	by all #unfold bound_iff.

lemma bound_elim1: for x if b: bound X (≤) b, x: x ∈ X then x ≤ b;
	by b[unfolded bound_iff, THEN allIn_elim1, OF x].

obtain extreme where extreme_iff: extreme X (≤) e ⟺ bound X (≤) e ∧ e ∈ X;
	- for thesis if assm;
		apply abbrev3[of (p. bound (fst p) (fst (snd p)) (snd (snd p)) ∧ snd (snd p) ∈ fst p)];
		- for f if (simp);
			apply assm[of f]; .
		.
	.
lemma extreme_closed: extreme X (≤) e ⟹ e ∈ X;
	simp extreme_iff.
lemma extreme_imp_bound: extreme X (≤) e ⟹ bound X (≤) e;
	simp extreme_iff.

obtain well_related where
	well_related_iff: well_related A (≤) ⟺ (∀X ⊆ A. X ≠ {} ⟹ ∃b ∈ X. bound X (dual (≤)) b);
	- for thesis if assm;
		apply abbrev2[of (p. ∀X ⊆ fst p. X ≠ {} ⟹ ∃b ∈ X. bound X (dual (snd p)) b)];
		- for f if (simp);
			apply assm[of f].
		.
	.

obtain monotone where
	monotone_iff: monotone A (≤) (⊑) f ⟺ (∀x ∈ A. ∀y ∈ A. x ≤ y ⟹ f x ⊑ f y);
	- for thesis if assm;
		apply abbrev4[of (p. ∀x ∈ fst p. ∀y ∈ fst p. fst (snd p) x y ⟹ fst (snd (snd p)) (snd (snd (snd p)) x) (snd (snd (snd p)) y))];
		- for f if (simp);
			apply assm[of f].
		.
	.
note monotone_elim1: monotone_iff[THEN iff_elim1, THEN allIn_elim1, THEN allIn_elim1].

---
## Some Collections

Here we define some collections.
Note that we do not define binary operators here:
one can obtain them so that the membership is as expected, but we need extensionality to
ensure that they are *equal* to the collection.

### Singleton
---
syntax {_} := singleton.
obtain singleton where singleton_def: {x} = {y. x = y};
	- for thesis if assm;
		apply abbrev[of (x. {y. x = y})];
		- for f if f;
			by assm[of f] #unfold f.
		.
	.

lemma in_singleton_iff(simp) x ∈ {y} ⟺ x = y;
	unfold singleton_def in_Collect_iff;
	apply iff.eq.commute.

lemma singleton_in_COLLECT! {x} ∈ COLLECT;
	unfold singleton_def;
	apply Collect_in_COLLECT.
---
### Big Union
---
obtain (⋃) where bigcup_def: ⋃XX = {x. ∃X ∈ XX. x ∈ X};
	- for thesis if assm;
		apply abbrev[of (XX. {x. ∃X ∈ XX. x ∈ X})];
		- for f if f;
			by assm[of f] #unfold f.
		.
	.

lemma bigcup_in_COLLECT! ⋃XX ∈ COLLECT;
	unfold bigcup_def;
	apply Collect_in_COLLECT.

lemma in_bigcup_iff: x ∈ ⋃XX ⟺ (∃X ∈ XX. x ∈ X);
	unfold bigcup_def in_Collect_iff.

lemma in_bigcup_intro1: for X if x: x ∈ X, X: X ∈ XX then x ∈ ⋃XX;
	unfold in_bigcup_iff;
	by exIn_intro1[of X] x X.

note in_bigcup_elim1: in_bigcup_iff[THEN iff_elim1].

lemma allIn_bigcup_iff(simp) (∀x ∈ ⋃XX. P.[x]) ⟺ (∀X ∈ XX. ∀x ∈ X. P.[x]);
	unfold bigcup_def allIn_Collect_iff;
	simp allIn_iff imp_all_iff;
	apply iff_intro;
	- if l for X x; by l[of x X].
	- if r for x X; by r[of X x].
	.

lemma bigcup_subseteq_iff: ⋃XX ⊆ Y ⟺ (∀X ∈ XX. X ⊆ Y);
	simp subseteq_iff_allIn.

lemma bigcup_subseteq_iff_bound: ⋃XX ⊆ X ⟺ bound XX (⊆) X;
	unfold bigcup_subseteq_iff bound_iff.

---
### Big Intersection
---
obtain (⋂) where bigcap_def: ⋂XX = {x. ∀X ∈ XX. x ∈ X};
	- for thesis if assm;
		apply abbrev[of (XX. {x. ∀X ∈ XX. x ∈ X})];
		- for f if f;
			by assm[of f] #unfold f.
		.
	.

lemma bigcap_in_COLLECT! ⋂XX ∈ COLLECT;
	unfold bigcap_def;
	apply Collect_in_COLLECT.

lemma in_bigcap_iff_allIn: x ∈ ⋂XX ⟺ (∀X ∈ XX. x ∈ X);
	by #unfold bigcap_def in_Collect_iff.

note in_bigcap_iff: in_bigcap_iff_allIn[unfolded allIn_iff].

lemma in_bigcap_intro: if all: ∀X. X ∈ XX ⟹ x ∈ X then x ∈ ⋂XX;
	by in_bigcap_iff[THEN iff_elim2] all.

lemma in_bigcap_elim1: if x: x ∈ ⋂XX, X: X ∈ XX then x ∈ X;
	by x[unfolded in_bigcap_iff, OF X].

lemma subseteq_bigcap_iff_allIn: X ⊆ ⋂YY ⟺ (∀Y ∈ YY. X ⊆ Y);
	by iff_intro #unfold subseteq_iff_allIn in_bigcap_iff allIn_iff.

note subseteq_bigcap_iff: subseteq_bigcap_iff_allIn[unfolded allIn_iff].

---
### Power Set
---
obtain Pow where Pow_def: Pow X = {Y. Y ⊆ X};
	- for thesis if assm;
		apply abbrev[of (X. {Y. Y ⊆ X})];
		- for f if f;
			by assm[of f] #unfold f.
		.
	.

lemma Pow_in_COLLECT! Pow X ∈ COLLECT;
	unfold Pow_def;
	by Collect_in_COLLECT.

lemma in_Pow_iff(simp) X ∈ Pow Y ⟺ X ⊆ Y;
	by #unfold Pow_def in_Collect_iff.
