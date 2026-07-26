fix (=).
assume eq_iff_all: x = y ⟺ (∀P. P.[x] ⟹ P.[y]).

begin

interpret base? Std.Eq;
	by #simp eq_iff_all.

interpret iff_eq: iff.MetaCommutative (=);
	by iff_intro[OF eq.sym eq.sym].

lemma eq_imp_iff#cong? if eq: P = Q then P ⟺ Q;
	unfold[on (=)] eq.

lemma all_eq_imp_iff: (∀x. x = a ⟹ P.[x]) ⟺ P.[a];
	apply iff_intro;
	- if all;
		apply all.
	- if Pa: P.[a], xa: x = a;
		by Pa #simp xa.
	.

interpret True.

lemma eq_refl_iff#simp x = x ⟺ true;
	by iff_intro.

---
Bounded quantifiers admit convenient congruence rules.
---
extend AllRel begin

	lemma all_cong:
		if ab: a = b, PQ: ∀x. x ⊏ b ⟹ P.[x] ⟺ Q.[x]
		then (∀x ⊏ a. P.[x]) ⟺ (∀x ⊏ b. Q.[x]);
		apply iff_intro;
		- if Pa;
			apply all_intro;
			by all_elim1[OF Pa, unfold ab] #fold PQ.
		- if Qb;
			apply all_intro;
			by all_elim1[OF Qb] #simp ab PQ.
		.
	lemma all_eq_imp_iff: (∀x ⊏ a. x = b ⟹ P.[x]) ⟺ (b ⊏ a ⟹ P.[b]);
		have 1: (∀x ⊏ a. x = b ⟹ P.[x]) ⟺ (∀x. x = b ⟹ x ⊏ a ⟹ P.[x]);
			unfold all_iff;
			by iff_intro.
		unfold 1;
		unfold all_eq_imp_iff.

end

extend ExRel begin

	lemma ex_cong:
		if ab: a = b, PQ: ∀x. x ⊏ b ⟹ P.[x] ⟺ Q.[x]
		then (∃x ⊏ a. P.[x]) ⟺ (∃x ⊏ b. Q.[x]);
		-	apply iff_intro;
			- if Pa;
				apply ex_elim[OF Pa];
				- for x;
					by ex_intro1[of x] #simp ab PQ[dual].
				.
			- if Qb;
				apply ex_elim[OF Qb];
				- for x;
					by ex_intro1[of x] #simp ab PQ.
				.
			.
		.
	lemma ex_eq_iff: (∃x ⊏ a. x = b) ⟺ b ⊏ a;
		apply iff_intro;
		unfold ex_imp_iff;
		- if xa: x ⊏ a, xb: x = b;
			by xa[unfold xb].
		- if ba: b ⊏ a;
			apply ex_intro1[OF _ ba].
		.

end

extend Iff.And begin

	extend Eq.ExRel begin

		lemma ex_eq_and_iff: (∃x ⊏ a. x = b ∧ P.[x]) ⟺ (b ⊏ a ∧ P.[b]);
			simp ex_iff_all;
			unfold imp_imp_commute;
			unfold all_eq_imp_iff and_iff.

	end

end

extend Iff.Ex begin

	extend And begin

		lemma ex_eq_and_iff: (∃x. x = a ∧ P.[x]) ⟺ P.[a];
			apply iff_intro;
			-> if xa: x = a, Px: P.[x];
				by Px #fold xa.
			- if Pa: P.[a];
				by ex_intro1[of a] Pa.
			.
		lemma ex_eq_and_iff2: (∃x. a = x ∧ P.[x]) ⟺ P.[a];
			unfold iff_eq.commute;
			by ex_eq_and_iff.

	end

end

theory Ex1 :=
	fix (∃!).
	assume ex1_iff_all: (∃!x. P.[x]) ⟺ (∀Q. (∀x. P.[x] ⟹ (∀y. P.[y] ⟹ y = x) ⟹ Q) ⟹ Q).
begin

	interpret base.Ex1;
		- for x P if Px: P.[x], u: ∀y. P.[y] ⟹ y = x then ∃!x. P.[x];
			unfold ex1_iff_all;
			- for Q if assm;
				by assm[of x] Px u.
			.
		- if ex1: ∃!x. P.[x], all: ∀x. P.[x] ⟹ (∀y. P.[y] ⟹ y = x) ⟹ Q then Q;
			apply ex1[unfold ex1_iff_all, OF all].
		.

	lemma ex1_cong#cong
		if iff: ∀x. P.[x] ⟺ P'.[x] then (∃!x. P.[x]) ⟺ (∃!x. P'.[x]);
		unfold ex1_iff_all iff.

	note#simp iff_true[OF ex1_eq1] iff_true[OF ex1_eq2].

	lemma ex1_imp_iff_eq: if ex1: ∃!x. P.[x], Px: P.[x] then P.[y] ⟺ x = y;
		apply iff_intro;
		- if Py; unfold ex1_imp_eq[OF ex1 Px Py].
		- if eq;
			by Px[unfold eq].
		.

	extend Iff.And begin

		lemma ex1_eq_and_iff: (∃!x. x = a ∧ P.[x]) ⟺ P.[a];
			simp ex1_iff_all and.left_assoc all_eq_imp_iff.

	end

end

extend MetaPair begin

	lemma all_pair: (∀(x,y). P.[x,y]) ⟺ (∀x y. P.[x,y]);
		apply iff_intro;
		- if pair for x y;
			by pair[of (x,y), simp].
		- if xy;
			by xy.
		.

	extend And begin

		lemma pair_eq_pair#simp (x,y) = (x',y') ⟺ x = x' ∧ y = y';
			apply iff_intro;
			- by #elim pair_eq_pair_elim.
			-> if x, y;
				simp x y.
			.

	end

end
