fix (∃).
assume ex_iff: (∃x. P.[x]) ⟺ (∀Q. (∀x. P.[x] ⟹ Q) ⟹ Q).

begin

interpret base? TypeFree.Ex;
	- for x if Px: P.[x];
		unfold ex_iff;
		- for Q if assm;
			apply assm[OF Px].
		.
	- for P if ex;
		apply ex[unfold ex_iff]=.
	.

lemma ex_imp_iff_all#simp#rule ((∃x. P.[x]) ⟹ Q) ⟺ (∀x. P.[x] ⟹ Q);
	apply iff_intro;
	- if imp: (∃x. P.[x]) ⟹ Q, Px: P.[x];
		by imp ex_intro1[OF Px].
	- if imp: ∀x. P.[x] ⟹ Q;
		by #elim imp ex_elim.
	.

lemma ex_cong#cong#rule_cong if eq: ∀x. P.[x] ⟺ P'.[x] then (∃x. P.[x]) ⟺ (∃x. P'.[x]);
	unfold ex_iff eq.

lemma ex_indep#simp (∃x. P) ⟺ P;
	by iff_intro ex_intro1 #elim ex_elim.

extend And begin

	lemma ex_and1#rule (∃x. P.[x]) ∧ Q ⟺ (∃x. P.[x] ∧ Q);
		simp iff_iff_and imp_and_distrib;
		- for x;
			by ex_intro1[of x].
		.

	lemma ex_and2#rule P ∧ (∃x. Q.[x]) ⟺ (∃x. P ∧ Q.[x]);
		simp iff_iff_and imp_and_distrib;
		- for x;
			by ex_intro1[of x].
		.

end

extend Or begin

	lemma ex_or_distrib: (∃x. P.[x] ∨ Q.[x]) ⟺ (∃x. P.[x]) ∨ (∃x. Q.[x]);
		apply iff_intro;
		-> for x if or;
			apply or_elim[OF or];
			by ex_intro1[of x].
		- if or;
			apply or_elim[OF or];
			-> for x; by ex_intro1[of x].
			-> for x; by ex_intro1[of x].
			.
		.

end

extend Not begin

	extend MinimalNot begin

		lemma nex_iff_all_not: ¬ (∃x. P.[x]) ⟺ (∀x. ¬ P.[x]);
			unfold not_iff_imp_not_true.

	end

end

---
## Theories
---
extend MetaRelation begin

	extend ExRel begin
		lemma ex_elim: if ex: ∃x ⊏ a. P.[x], imp: ∀x. x ⊏ a ⟹ P.[x] ⟹ Q then Q;
			apply ex[unfold ex_iff, THEN ex_elim];
			- for x;
				by imp[of x].
			.
		lemma ex_cong_strong:
			if a: ∀x. x ⊏ a ⟺ x ⊏ a', P: ∀x. x ⊏ a' ⟹ (P.[x] ⟺ P'.[x])
			then (∃x ⊏ a. P.[x]) ⟺ (∃x ⊏ a'. P'.[x]);
			unfold+ ex_iff; unfold a; unfold P.

		lemma ex_cong_weak:
			if P: ∀x. x ⊏ a ⟹ (P.[x] ⟺ P'.[x]) then (∃x ⊏ a. P.[x]) ⟺ (∃x ⊏ a. P'.[x]);
			unfold+ ex_iff P.

		lemma ex_imp_iff: ((∃x ⊏ a. P.[x]) ⟹ Q) ⟺ (∀x. x ⊏ a ⟹ P.[x] ⟹ Q);
			apply iff_intro;
			- if imp, x: x ⊏ a, Px: P.[x];
				apply imp ex_intro1[OF x Px].
			- if all, ex;
				apply ex_elim[OF ex];
				- for x if x, Px;
					apply all[OF x Px].
				.
			.
		lemma ex_or_distrib: (∃x ⊏ a. P.[x] ∨ Q.[x]) ⟺ (∃x ⊏ a. P.[x]) ∨ (∃x ⊏ a. Q.[x]);
			simp ex_iff and_or_distrib .ex_or_distrib.

		lemma ex_iff_all: (∃x ⊏ a. P.[x]) ⟺ (∀Q. (∀x. x ⊏ a ⟹ P.[x] ⟹ Q) ⟹ Q);
			unfold ex_iff Minimal.ex_iff.

	end

	extend AllRel begin -- TODO: automate?
		extend ExRel begin
			lemma ex_imp_iff_all: ((∃x ⊏ a. P.[x]) ⟹ Q) ⟺ (∀x ⊏ a. P.[x] ⟹ Q);
				simp ex_iff all_iff ex_imp_iff.
			lemma nex_iff_all_not: ¬ (∃x ⊏ a. P.[x]) ⟺ (∀x ⊏ a. ¬ P.[x]);
				unfold ex_iff all_iff .nex_iff_all_not nand_iff_imp_not.
		end
	end
end

extend Membership begin
	interpret in: Minimal.MetaRelation (∈).
	interpret in: in.AllRel (∀∈).
	interpret in: in.ExRel (∃∈).

	note#rule in.all_iff.
	note#rule in.ex_imp_iff.
	note#simp in.ex_imp_iff_all.
	note#elim in.ex_elim.

end
