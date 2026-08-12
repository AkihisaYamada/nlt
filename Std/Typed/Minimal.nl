---
## Propositional Minimal Logic
---
import True, And, Or, Not, MinimalNot, Iff.

begin

instance Iff.True.

lemma not_cong#cong if PQ: P ⟺ Q, [P : Prop, Q : Prop] then ¬ P ⟺ ¬ Q;
	by iff_intro #elim not_imp_imp_not #simp PQ.

lemma or_cong#cong
	if P: P ⟺ P', Q: Q ⟺ Q', [P : Prop, Q : Prop, P' : Prop, Q' : Prop]
	then P ∨ Q ⟺ P' ∨ Q';
	apply iff_intro;
	- if PQ; apply or_elim[OF PQ];
		- by or_intro1 #simp P.
		- by or_intro2 #simp Q.
		.
	- if PQ'; apply or_elim[OF PQ'];
		- by or_intro1 #simp P[dual].
		- by or_intro2 #simp Q[dual].
		.
	.

lemma not_iff_imp_not_true: if [P : Prop] then ¬P ⟺ (P ⟹ ¬true);
	apply iff_intro;
	- by #elim not_elim_not.
	- if P0; apply imp_not_imp_not;
		- if P;
			apply not_elim_not[OF P0[OF P]].
		.
	.

extend Quantifiable begin

	lemma all_cong_weak:
		if PQ: ∀x. x : A ⟹ P.[x] ⟺ Q.[x],
			[A : QTYPE, ∀x. x : A ⟹ P.[x] : Prop, ∀x. x : A ⟹ Q.[x] : Prop]
		then (∀x : A. P.[x]) ⟺ (∀x : A. Q.[x]);
		apply iff_intro;
		- if P;
			apply all_intro;
			- if x! x : A;
				fold[on (⟺)] PQ[OF x];
				by P[THEN all_elim1].
			.
		- if Q;
			apply all_intro;
			- if x! x : A;
				unfold[on (⟺)] PQ[OF x];
				by Q[THEN all_elim1].
			.
		.

	lemma ex_cong_weak:
		if PQ: ∀x. x : A ⟹ P.[x] ⟺ Q.[x],
			[A : QTYPE, ∀x. x : A ⟹ P.[x] : Prop, ∀x. x : A ⟹ Q.[x] : Prop]
		then (∃x : A. P.[x]) ⟺ (∃x : A. Q.[x]);
		apply iff_intro;
		- if P; apply P[THEN ex_elim];
			- if Px: P.[x], ...;
				apply ex_intro1[OF Px[unfold[on (⟺)] PQ]].
			.
		- if Q; apply Q[THEN ex_elim];
			- if Qx: Q.[x], ...;
				apply ex_intro1[OF Qx[fold[on (⟺)] PQ]].
			.
		.

	lemma ex_imp_iff_all_imp#simp
		if [A : QTYPE, Q : Prop, ∀x. x : A ⟹ P.[x] : Prop]
		then ((∃ x : A. P.[x]) ⟹ Q) ⟺ (∀ x : A. P.[x] ⟹ Q);
		apply iff_intro;
		- if ex_imp; apply all_intro;
			- if [x : A], Px;
				apply ex_imp;
				by ex_intro1[OF Px].
			.
		- if all_imp, ex;
			apply ex_elim[OF ex];
			- if Px: P.[x], ...;
				apply all_imp[THEN all_elim1[of x]];
				by Px.
			.
		.

	lemma nex_iff_all_not#simp
		if [A : QTYPE, ∀x. x : A ⟹ P.[x] : Prop]
		then ¬(∃x : A. P.[x]) ⟺ (∀x : A. ¬ P.[x]);
		unfold not_iff_imp_not_true ex_imp_iff_all_imp.

end

extend FirstOrder begin

	instance Quantifiable IND.

end

extend SecondOrder begin

	instance Quantifiable.

end

extend HigherOrder begin

	instance Quantifiable.

end

extend Std.Membership begin--TODO: automate?

	instance ContraPos.Membership.
	instance Or.Membership.

end

instance Membership (:).
