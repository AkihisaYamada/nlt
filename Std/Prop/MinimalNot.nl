import Not.

assume imp_not_sym: if P ⟹ ¬Q, Q, P : Prop, Q : Prop then ¬P.

begin

lemma not_intro_connect: if P: P, QnP: Q ⟹ ¬P, [P : Prop, Q : Prop] then ¬Q;
	apply imp_not_sym[OF QnP P].

lemma nnot_intro: if P: P, [P : Prop] then ¬ ¬ P;
	apply not_intro_connect[OF P].

instance ContraPos;
	- if nQ: ¬Q, PQ: P ⟹ Q, ... then ¬P;
		apply not_intro_connect[OF nQ];
		by nnot_intro PQ.
	.

theorem nnnot_elim: -- @English Triple Negation Elimination
	if nnnP: ¬ ¬ ¬ P, [P : Prop] then ¬P;
	apply not_imp_imp_not[OF nnnP];
	by nnot_intro.

instance SelfRefutation;
	- if 1: P ⟹ ¬P, ... then ¬P;
		have 2: P ⟶ ¬P; apply imp_intro, 1>0.
		apply not_intro_connect[OF 2];
		by nimp_intro nnot_intro.
	.

lemma not_intro_contr:-- @English negation introduction
	for Q if PQ: P ⟹ Q, PnQ: P ⟹ ¬Q, [P : Prop, Q : Prop] then ¬P;
	apply imp_not_imp_not;
	- if P;
		apply not_elim_not[of Q];
		by PQ PnQ P.
	.

-- `(¬ ¬ P ⟹ ¬Q) ⟺ (P ⟹ ¬Q)`
lemma nnot_imp_imp: if imp: ¬ ¬ P ⟹ Q, P: P, [P : Prop, Q : Prop] then Q;
	use P; by imp nnot_intro.

-- If the conclusion is negated, one can eliminate double negation.
lemma nnot_elim_not: if nnP: ¬ ¬ P, PnQ: P ⟹ ¬Q, [P : Prop, Q : Prop] then ¬Q;
	apply imp_not_sym[OF _ nnP];
	by nnot_intro imp_not_sym[OF PnQ].

lemma nimp_not_intro: if nnP: ¬ ¬ P, nnQ: ¬ ¬ Q, [P : Prop, Q : Prop] then ¬(P ⟶ ¬Q);
	apply nnot_elim_not[OF nnP];
	by nimp_intro nnQ.

-- Double negated implication works as implication of double negation. 
lemma nnimp_elim_nnot: if nnPQ: ¬ ¬ (P ⟶ Q), nnP: ¬ ¬ P, [P : Prop, Q : Prop] then ¬ ¬ Q;
	apply nnot_elim_not[OF nnPQ];
	- if PQ;
		apply nnot_elim_not[OF nnP];
		by nnot_intro PQ[THEN imp_elim1].
	.

extend ExRelStrict begin

	lemma nex_intro:
		if all_not: ∀x. x ⊏ a ⟹ ¬ P.[x], [a : A, ∀x. x ⊏ a ⟹ P.[x] : Prop]
		then ¬(∃x ⊏ a. P.[x]);
		apply imp_not_imp_not;
		- if ex: ∃x ⊏ a. P.[x];
			apply ex_elim[OF ex];
			- for x if Px: P.[x], xa! x ⊏ a;
				by not_elim_not[OF all_not[OF xa] Px].
			.
		.

end
