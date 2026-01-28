---
# Fixed Points
---
import Collection.

begin

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

