base QuantifiedIntuitionistic.

import ..Nat.

import eq_nat: Binary (=) nat nat prop.

begin

setup rewrite eq_prop1 eq_prop2 eq.refl eq.trans.
setup dual eq.sym.

setup define beta.

note! eq_nat.type.

lemma suc_eq_suc_iff: if ! nat x, ! nat y then suc x = suc y ⟺ x = y;
	apply iff_intro,
	- by suc_inj.
	- if xy: x = y;
		by #unfold(=) xy.
	.

lemma induction_all:
	if 0: α.[0], suc: ∀x. α.[x] ⟹ nat x ⟹ α.[suc x], [∀x. nat x ⟹ prop α.[x]]
	then ∀x:nat. α.[x];
	apply all_intro,
	by induction[OF 0 suc].

lemma zero_neq_suc: if !nat x then ¬ 0 = suc x;
	apply not_intro,
	- if eq: 0 = suc x;
		define test := case true (λx. false).
		have 1: test 0;
			by #unfold(=)+ test_def case_zero.
		have 2: test (suc x);
			by 1[unfolded(=) eq].
		by 2[unfolded(=)+ test_def case_suc beta].
	.

lemma zero_eq_suc_iff: if ! nat x then 0 = suc x ⟺ false;
	by not_imp_iff_false zero_neq_suc.

obtain (<) where
	less_zero: nat x ⟹ (x < 0) = false,
	zero_less_suc: nat x ⟹ (0 < suc x) = true,
	suc_less_suc: nat x ⟹ nat y ⟹ (suc x < suc y) = (x < y);
	- for thesis, if assm:;
		apply assm(λx y. case false (λz. true) (y ∸ x)),
		- for x, if ! nat x;
			unfold(=)+ beta zero_diff case_zero,
			by not_false.
		- for x, if ! nat x;
			unfold(=)+ beta diff_zero case_suc.
		- for x y, if ! nat x, ! nat y;
			unfold(=)+ beta suc_diff_suc.
		.
	.


interpret less: Binary (<) nat nat prop;
	show: ∀x y. nat x ⟹ nat y ⟹ prop (x < y);
		have 1: ∀y. nat y ⟹ ∀x. nat x ⟹ prop (x < y);
			apply induction!2,
			- by #unfold(=) less_zero.
			- for y, if IH:, !;
				apply induction!2,
				by IH #unfold(=) zero_less_suc suc_less_suc.
			.
		by 1.
	.

note! less.type.

interpret less: Irreflexive nat (<);
	show: ∀x. nat x ⟹ ¬ x < x;
		apply induction!2,
		by not_false #unfold(=) less_zero suc_less_suc.
	.

lemma less_succ: ∀x y. nat x ⟹ nat y ⟹ (x < suc y) = case true (λx'. x' < y) x;
	have 1: ∀x. nat x ⟹ ∀y. nat y ⟹ (x < suc y) = case true (λx'. x' < y) x;
		apply induction!2,
		by #unfold(=) case_zero case_suc zero_less_suc suc_less_suc beta.
	by 1.

lemma zero_less_iff_ex: ∀x. nat x ⟹ 0 < x ⟺ (∃y:nat. x = suc y);
	apply induction!2,
	- unfold(=) less_zero,
		by #unfold(⟺) zero_eq_suc_iff ex_false_iff.
	- for x, if IH:, !;
		unfold(=) zero_less_suc,
		by true_iff ex_intro1(x).
	.

lemma less_suc_infl: ∀x. nat x ⟹ x < suc x;
	apply induction!2,
	- by #unfold(=) zero_less_suc.
	- for x, if IH:, !;
		by IH #unfold(=) suc_less_suc.
	.

lemma suc_less_lemma:
	∀x:nat. ∀y:nat. (suc x < y ⟹ x < y) ∧ (x < y ⟹ x < suc y);
	apply induction_all,
	- apply induction_all,
		- by and_intro #unfold(=) less_zero zero_less_suc.
		- for y, if IH:, !;
			by and_intro #unfold(=) zero_less_suc.
		.
	- for x, if IHx:, !;
		apply induction_all,
		- by and_intro #unfold(=)+ less_zero suc_less_suc.
		- for y, if IHy:, !;
			unfold(=) suc_less_suc,
			by all_elim1[OF IHx](y).
		.
	.

lemma suc_less_imp_less: if sxy: suc x < y, xt! nat x, yt! nat y then x < y;
	have 1: ∀y:nat. (suc x < y ⟹ x < y) ∧ (x < y ⟹ x < suc y);
		by all_elim1[OF suc_less_lemma].
	have 2: (suc x < y ⟹ x < y) ∧ (x < y ⟹ x < suc y);
		by all_elim1[OF 1].
	by and_elim1[OF 2] sxy.

lemma less_imp_less_suc: if xy: x < y, xt! nat x, yt! nat y then x < suc y;
	have 1: ∀y:nat. (suc x < y ⟹ x < y) ∧ (x < y ⟹ x < suc y);
		by all_elim1[OF suc_less_lemma].
	have 2: (suc x < y ⟹ x < y) ∧ (x < y ⟹ x < suc y);
		by all_elim1[OF 1].
	by and_elim2[OF 2] xy.

lemma suc_less_iff_ex: ∀x y. nat x ⟹ nat y ⟹ suc x < y ⟺ (∃z:nat. y = suc z ∧ x < z);
	have 1: for x, if !nat x then ∀y. nat y ⟹ suc x < y ⟺ (∃z:nat. y = suc z ∧ x < z);
		apply induction!2,
		- unfold(=) less_zero,
			unfold(⟺)+ zero_eq_suc_iff false_and_iff ex_false_iff.
		- for y, if IH:, !;
			unfold(=) suc_less_suc,
			apply iff_intro,
			- if xy: x < y;
				apply ex_intro1(y),
				by and_intro less_imp_less_suc xy #unfold(⟺) suc_eq_suc_iff.
			- if ex:;
				apply ex_elim[OF ex],
				- for z, if assm: suc y = suc z ∧ x < z, ! nat z;
					have sysz: suc y = suc z;
						by and_elim1[OF assm].
					have yz: y = z;
						by sysz[unfolded(⟺) suc_eq_suc_iff].
					have xz: x < z;
						by and_elim2[OF assm].
					by xz #unfold(=) yz.
				.
			.
		.
	by 1.

interpret less: Transitive nat (<);
	have 1: ∀x. nat x ⟹ ∀y. nat y ⟹ ∀z. nat z ⟹ x < y ⟹ y < z ⟹ x < z;
		apply induction!2,
		- apply induction!2,
			- apply induction!2,
				unfold(=) less_zero.
			- for y, if IHy:,!;
				apply induction!2,
				- unfold(=) less_zero suc_less_suc zero_less_suc.
				- by #unfold(=) zero_less_suc.
				.
			.
		- for x, if IHx:,!;
			- apply induction!2,
				- for z, if !;
					unfold(=) less_zero,
					by #elim false_elim.
				- for y, if IHy:, yt!;
					apply induction!2,
					- unfold(=) less_zero,
						by #elim false_elim.
					- for z, if IHz:, zt!;
						unfold(=) suc_less_suc,
						apply IHx[OF yt zt]=.
					.
				.
			.
		.
	by 1.
