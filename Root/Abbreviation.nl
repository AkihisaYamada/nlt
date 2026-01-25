---
# Type-Free Intuitionistic Logic via Binary Abbreviation
---
import Eq.
import Pair.
assume abbrev2: if ∀f. (∀x y. f x y = F.[(x,y)]) ⟹ P then P.

begin

--- Binary abbreviation allows unary and multi-ary abbreviations. ---
interpret UnaryAbbreviation;
	- for F P if assm;
		note(cong) eq.cong_meta[of F].
		apply abbrev2[of (p. F.[snd p])];
		- for f if f;
			by assm[of (f fst)] #unfold f.
		.
	.

lemma abbrev3: if assm: ∀f. (∀x y z. f x y z = F.[(x,y,z)]) ⟹ P then P;
	apply abbrev2[of (t. F.[(fst (fst t), snd (fst t), snd t)])];
	- for f2 if (simp);
		apply abbrev2[of (p. f2 p)];
		- for f3 if (simp);
			by assm[of f3] #cong eq.cong_meta[of F].
		.
	.
lemma abbrev4: if assm: ∀f. (∀x y z w. f x y z w = F.[(x,y,z,w)]) ⟹ P then P;
	apply abbrev2[of (t. F.[(fst (fst (fst t)), snd (fst (fst t)), snd (fst t), snd t)])];
	- for f2 if (simp);
		apply abbrev2[of (p. f2 p)];
		- for f3 if (simp);
			apply abbrev2[of (p. f3 p)];
			- for f4 if (simp);
				by assm[of f4] #cong eq.cong_meta[of F].
			.
		.
	.

--- One can obtain type-free binary logical operators by abbreviation. ---
interpret Iff;
	obtain (⟺) where
		iff_intro: if P ⟹ Q, Q ⟹ P then P ⟺ Q,
		iff_elim1: if P ⟺ Q, P then Q,
		iff_elim2: if P ⟺ Q, Q then P;
		- for thesis if assm;
			apply abbrev2[of (p. ∀R. ((fst p ⟹ snd p) ⟹ (snd p ⟹ fst p) ⟹ R) ⟹ R)];
			- for f if f;
				apply assm[of f];
				- for P Q if PQ, QP;
					unfold f;
					- for R if body;
						apply body;
						-; by PQ.
						-; by QP.
						.
					.
				- for P Q if fPQ, P;
					apply fPQ[unfolded f];
					simp;
					- if PQ, QP;
						by PQ[OF P].
					.
				- for P Q if fPQ, Q;
					apply fPQ[unfolded f];
					simp;
					- if PQ, QP;
						by QP[OF Q].
					.
				.
			.
		.
	.

interpret Intuitionistic;
	obtain true where true_intro: true;
		- for thesis if assm;
			apply assm[of (∀P. P ⟹ P)].
		.
	obtain false where false_elim: if false then P;
		- for thesis if assm;
			apply assm[of (∀P. P)].
		.
	obtain (∧) where
		and_intro: for P Q if P, Q then P ∧ Q,
		and_elim1: if P ∧ Q then P,
		and_elim2: if P ∧ Q then Q;
		- for thesis if assm;
			apply abbrev2[of (p. ∀R. (fst p ⟹ snd p ⟹ R) ⟹ R)];
			- for f if f;
				apply assm[of f, unfolded f fst snd].
			.
		.
	obtain (∨) where
		or_intro1: for P Q if P then P ∨ Q,
		or_intro2: for P Q if Q then P ∨ Q,
		or_elim: if P ∨ Q, P ⟹ R, Q ⟹ R then R;
		- for thesis if assm;
			apply abbrev2[of (p. ∀R. (fst p ⟹ R) ⟹ (snd p ⟹ R) ⟹ R)];
			- for f if f;
				apply assm[of f, unfolded f fst snd];
				-; by #unfold imp_imp_iff.
				-; by #unfold imp_imp_iff.
				- for P Q; apply imp.refl>0.
				.
			.
		.
	obtain (¬) where
		not_intro: if P ⟹ false then ¬P,
		not_imp_false: if ¬P, P then false;
		- for thesis if assm;
			apply abbrev[of (P. P ⟹ false)];
			- for f if f;
				apply assm[of f, unfolded f].
			.
		.
	.

interpret Const;
	obtain const where const_eq: const x y = x;
		- for thesis if assm;
			apply abbrev2[of (p. fst p)];
			- for f if f;
				by assm[of f] #unfold f.
			.
		.
	.

interpret Dual;
	obtain dual where dual_eq: dual f x y = f y x;
		- for thesis if assm;
			apply abbrev3[of (p. fst p (snd (snd p)) (fst (snd p)))];
			- for f if (simp);
				apply assm[of f].
			.
		.
	.

lemma curry: for f, ∃f'. ∀x y. f' x y = f (x,y);
	apply abbrev2[of (p. f p)];
	- for f' if f';
		by ex_intro1[of f'] #unfold f'.
	.
obtain inverts where
	inverts_intro: if ∀x. f (g x) = x then inverts f g,
	inverts_elim1: if inverts f g then f (g x) = x;
	- for thesis if assm;
		apply abbrev2[of (p. ∀x. fst p (snd p x) = x)];
		- for f if f;
			by assm[of f] #unfold f.
		.
	.
obtain rev_app where rev_app: rev_app x f = f x;
	- for thesis if assm;
		apply abbrev2[of (p. snd p (fst p))];
		- for f if f;
			by assm[of f] #unfold f.
		.
	.

obtain (≠) where neq_iff: x ≠ y ⟺ ¬ x = y;
	- for thesis if assm;
		apply abbrev2[of (p. ¬ fst p = snd p)];
		- for f if f;
			by assm[of f] #unfold f.
		.
	.
lemma neq_intro: (x = y ⟹ false) ⟹ x ≠ y;
	unfold neq_iff not_iff_imp_false.

obtain sup_pred where sup_pred_iff: sup_pred P Q x ⟺ P x ∨ Q x;
	- for thesis if assm;
		apply abbrev3[of (t. fst t (snd (snd t)) ∨ fst (snd t) (snd (snd t)))];
		- for f if f;
			by assm[of f] #unfold f.
		.
	.
obtain inf_pred where inf_pred_iff: inf_pred P Q x ⟺ P x ∧ Q x;
	- for thesis if assm;
		apply abbrev3[of (t. fst t (snd (snd t)) ∧ fst (snd t) (snd (snd t)))];
		- for f if f;
			by assm[of f] #unfold f.
		.
	.
theory Membership:
	import Membership.
begin
	obtain (⊆) where subseteq_iff: X ⊆ Y ⟺ (∀x. x ∈ X ⟹ x ∈ Y);
		- for thesis if assm;
			apply abbrev2[of (p. ∀x. x ∈ fst p ⟹ x ∈ snd p)];
			- for f if f;
				by assm[of f] #unfold f.
			.
		.
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

	obtain (∉) where notin_iff: x ∉ X ⟺ ¬ x ∈ X;
		- for thesis if assm;
			apply abbrev2[of (p. ¬ fst p ∈ snd p)];
			- for f if f;
				apply assm[of f];
				by iff_intro #unfold f.
			.
		.
	obtain (∋) where has_iff_in(simp) X ∋ x ⟺ x ∈ X;
		- for thesis if assm;
			apply abbrev2[of (p. snd p ∈ fst p)];
			- for f if f;
				apply assm[of f];
				by iff_intro #unfold f.
			.
		.

end

theory Collect:
	import Membership.
	import Collect.
begin
	syntax {} := Empty.
	obtain Empty where Empty_def: {} = {x. false};
		- for thesis if assm;
			apply assm[OF eq.refl].
		.
	lemma not_in_Empty: ¬ x ∈ {};
		by #unfold Empty_def in_Collect_iff const_eq.

	syntax {_} := Singleton.
	obtain Singleton where Singleton_def: {x} = {y. x = y};
		- for thesis if assm;
			apply abbrev[of (x. {y. x = y})];
			- for f if f;
				by assm[of f] #unfold f.
			.
		.
	lemma in_Singleton_iff: x ∈ {y} ⟺ x = y;
		unfold Singleton_def in_Collect_iff;
		apply iff.eq.commute.

	obtain UNIV where UNIV_def: UNIV = {x. true};
		- for thesis if assm;
			apply assm[OF eq.refl].
		.
	lemma in_UNIV! x ∈ UNIV;
		unfold UNIV_def in_Collect_iff.

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

	obtain (⋃) where bigcup_def: ⋃XX = {x. ∃X ∈ XX. x ∈ X};
		- for thesis if assm;
			apply abbrev[of (XX. {x. ∃X ∈ XX. x ∈ X})];
			- for f if f;
				by assm[of f] #unfold f.
			.
		.
	lemma in_bigcup_iff: x ∈ ⋃XX ⟺ (∃X ∈ XX. x ∈ X);
		unfold bigcup_def in_Collect_iff.
	lemma in_bigcup_intro1: if x: x ∈ X, X: X ∈ XX then x ∈ ⋃XX;
		unfold in_bigcup_iff;
		by exIn_intro1[of X] x X.
	note in_bigcup_elim1: in_bigcup_iff[THEN iff_elim1].

	obtain (⋂) where bigcap_def: ⋂XX = {x. ∀X ∈ XX. x ∈ X};
		- for thesis if assm;
			apply abbrev[of (XX. {x. ∀X ∈ XX. x ∈ X})];
			- for f if f;
				by assm[of f] #unfold f.
			.
		.
	lemma in_bigcap_iff: x ∈ ⋂XX ⟺ (∀X ∈ XX. x ∈ X);
		by #unfold bigcap_def in_Collect_iff.
	lemma in_bigcap_intro: if all: ∀X. X ∈ XX ⟹ x ∈ X then x ∈ ⋂XX;
		by in_bigcap_iff[THEN iff_elim2] allIn_intro all.
	lemma in_bigcap_elim1: if x: x ∈ ⋂XX, X: X ∈ XX then x ∈ X;
		by x[unfolded in_bigcap_iff, THEN allIn_elim1, OF X].
	lemma subseteq_bigcap_iff: X ⊆ ⋂YY ⟺ (∀Y ∈ YY. X ⊆ Y);
		by iff_intro #unfold subseteq_iff in_bigcap_iff allIn_iff.
	---
	One can obtain union so that the membership is as expected, but we need extensionality to
	ensure that union is *equal* to the expected collection.
	---
	obtain (∪) where cup_eq_sup_pred: X ∪ Y = {x. sup_pred (X ∋) (Y ∋)};
		- for thesis if assm;
			apply abbrev2[of (p. {x. sup_pred (fst p ∋) (snd p ∋)})];
			- for f if (simp);
				apply assm[of f];
				oops
			oops
		oops

	obtain Pow where Pow_def: Pow X = {Y. Y ⊆ X};
		- for thesis if assm;
			apply abbrev[of (X. {Y. Y ⊆ X})];
			- for f if f;
				by assm[of f] #unfold f.
			.
		.
	lemma in_Pow_iff(simp) X ∈ Pow Y ⟺ X ⊆ Y;
		by #unfold Pow_def in_Collect_iff.

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

	obtain bound where bound_iff: bound X (≤) b ⟺ (∀x ∈ X. x ≤ b);
		- for thesis if assm;
			apply abbrev3[of (p. ∀x ∈ fst p. fst (snd p) x (snd (snd p)))];
			- for f if (simp);
				apply assm[of f].
			.
		.

	obtain extreme where extreme_iff: extreme X (≤) e ⟺ bound X (≤) e ∧ e ∈ X;
		- for thesis if assm;
			apply abbrev3[of (p. bound (fst p) (fst (snd p)) (snd (snd p)) ∧ snd (snd p) ∈ fst p)];
			- for f if (simp);
				apply assm[of f]; .
			.
		.

	obtain extreme_bound where
		extreme_bound_iff: extreme_bound A (≤) X s ⟺ extreme {b. b ∈ A ∧ bound X (≤) b} (dual (≤)) s;
		- for thesis if assm;
			apply abbrev4[of (p. extreme {b. b ∈ fst p ∧ bound (fst (snd (snd p))) (fst (snd p)) b} (dual (fst (snd p))) (snd (snd (snd p))))];
			- for f if (simp);
				apply assm[of f];
				simp extreme_iff bound_iff allIn_Collect_iff in_Collect_iff; .
			.
		.

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

	obtain complete where
		complete_iff: complete C A (≤) ⟺ (∀X ⊆ A. C X (≤) ⟹ ∃s. extreme_bound A (≤) X s);
		- for thesis if assm;
			apply abbrev3[of (p. (∀X ⊆ fst (snd p). fst p X (snd (snd p)) ⟹ ∃s. extreme_bound (fst (snd p)) (snd (snd p)) X s))];
			- for f if (simp);
				apply assm[of f].
			.
		.

end
---
Having operator `THE` yields `If`.
---
theory The:
	import The.
begin
	interpret If;
		obtain If where
			If_then: P ⟹ If P x y = x,
			If_else: (P ⟹ x = y) ⟹ If P x y = y;
			- for thesis if assm;
				apply abbrev3[of (t. THE z. fst t ∧ z = fst (snd t) ∨ (fst t ⟹ fst (snd t) = snd (snd t)) ∧ z = snd (snd t))];
				- for If if If;
					apply assm[of If, unfolded If];
					- for P x y if P: P;
						apply THE_eq_intro;
						-; unfold fst snd;
							apply ex1_intro1[of x];
							-; by or_intro1 P.
							- for z if or;
								apply or_elim[OF or];
								-; .
								-; unfold and_imp_iff_imp_imp imp_imp_iff[OF P];
									- if xy, zy;
										unfold xy zy.
									.
								.
							.
						-; unfold fst snd;
							by or_intro1 P.
						.
					- for P x y if nP: P ⟹ x = y;
						apply THE_eq_intro;
						-; unfold fst snd;
							apply ex1_intro1[of y];
							-; unfold imp_and_iff1[OF nP] or_iff_true2.
							- for z if or;
								apply or_elim[OF or];
								unfold and_imp_iff_imp_imp;
								- if P: P, zx: z = x then z = y;
									unfold nP[OF P] zx.
								.
							.
						-; unfold fst snd;
							by or_intro2 nP.
						.
					.
				.
			.
		.
end

end
