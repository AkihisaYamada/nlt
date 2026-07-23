import base? TypeFree.Ex.

begin

lemma ex_imp_iff_all#simp#rule ((∃x. P.[x]) ⟹ Q) ⟺ (∀x. P.[x] ⟹ Q);
	apply iff_intro;
	- if imp: (∃x. P.[x]) ⟹ Q, Px: P.[x];
		by imp ex_intro1[OF Px].
	- if imp: ∀x. P.[x] ⟹ Q;
		by #elim imp ex_elim.
	.

lemma ex_iff: (∃x. P.[x]) ⟺ (∀Q. (∀x. P.[x] ⟹ Q) ⟹ Q);
	apply iff_intro;
	-> for x if Px for Q if assm;
		apply assm[OF Px].
	- if assm;
		apply assm;
		- for x if Px; by ex_intro1[OF Px].
		.
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
			unfold not_true.not_iff_imp_false.

	end

end
