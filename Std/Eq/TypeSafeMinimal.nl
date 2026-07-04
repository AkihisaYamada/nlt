import Std.TypeSafeMinimal.
fix (∃!).
assume ex1_def: (∃!x. P.[x]) = (∃x. P.[x] ∧ (∀y. P.[y] ⟹ y = x)).
begin

lemma eq_refl_iff#simp x = x ⟺ true;
	by iff_intro.

interpret iff_eq: iff.MetaCommutative (=);
	by iff_intro[OF eq.sym eq.sym].

lemma eq_imp_iff#cong? if eq: P = Q then P ⟺ Q;
	unfold[on (=)] eq.

lemma all_eq_imp_iff: (∀x. x = a ⟹ P.[x]) ⟺ P.[a];
	apply iff_intro;
	- if all;
		apply all.
	- if Pa: P.[a], xa: x = a;
		note#cong eq_cong_meta[of P].
		by Pa #simp xa.
	.
lemma ex_eq1: ∃x. x = a;
	apply ex_intro1[of a].
lemma ex_eq2: ∃x. a = x;
	apply ex_intro1[of a].

lemma ex1_intro1: for x P if Px: P.[x], u: ∀y. P.[y] ⟹ y = x then ∃!x. P.[x];
	unfold ex1_def;
	by ex_intro1[of x] Px u.
lemma ex1_intro: if assm: ∀Q. (∀x. P.[x] ⟹ (∀y. P.[y] ⟹ y = x) ⟹ Q) ⟹ Q then ∃!x. P.[x];
	apply assm;
	- for x if Px;
		by ex1_intro1[OF Px].
	.
lemma ex1_eq1: ∃!x. x = a;
	apply ex1_intro1[of a].
lemma ex1_eq2: ∃!x. a = x;
	apply ex1_intro1[of a];
	-.
	- for x; apply eq.sym>0.
	.
theory UniqueChoiceOp:
	fix (such).
	assume such_intro_ex1: if ∃!x. P.[x] then P.[such x. P.[x]].
end

extend MetaRelation begin

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
				unfold all_def;
				by iff_intro.
			unfold 1;
			unfold all_eq_imp_iff.

	end

	theory Ex1Rel:
		fix (∃!⊏).
		assume ex1_def: (∃!x ⊏ a. P.[x]) ⟺ (∃!x. x ⊏ a ∧ P.[x]).
	begin
	end

end

extend Membership begin

	interpret in: MetaRelation (∈).

end

extend Pair begin
	lemma pair_eq_pair#simp (x,y) = (x',y') ⟺ x = x' ∧ y = y';
		apply iff_intro;
		- if eq;
			by pair_eq_pair_elim1[OF eq] pair_eq_pair_elim2[OF eq].
		simp;
		- if x, y;
			simp x y.
		.
	lemma all_pair: (∀(x,y). P.[x,y]) ⟺ (∀x y. P.[x,y]);
		apply iff_intro;
		note#cong eq_cong_meta[of P].
		- if pair for x y;
			by pair[of (x,y),simp].
		- if xy;
			by xy.
		.
end
