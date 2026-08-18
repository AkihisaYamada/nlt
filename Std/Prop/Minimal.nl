---
## Propositional Minimal Logic
---
import True, False, And, Or, Not, MinimalNot, Iff.

begin

lemma not_cong#cong if PQ: P ⟺ Q, [P : Prop, Q : Prop] then ¬ P ⟺ ¬ Q;
	by iff_intro #elim not_imp_imp_not #simp PQ.

instance and: iff.CommMonoidAbsorb (∧) false true;
	by iff_intro #elim iff_elim false_elim.

note#cong and.cong.
note#simp and.left_neutral and.right_neutral and.left_absorb and.right_absorb.

instance or: iff.CommMonoidAbsorb (∨) true false;
	- if [P : Prop, Q : Prop, R : Prop] then P ∨ Q ∨ R ⟺ P ∨ (Q ∨ R);
		apply iff_intro;
		- if PQR; apply or_elim[OF PQR];
			- if PQ; apply or_elim[OF PQ];
				- if P; apply or_intro1, P.
				- if Q; apply or_intro2, or_intro1, Q.
				.
			- if R; apply or_intro2, or_intro2, R.
			.
		- if PQR; apply or_elim[OF PQR];
			- if P; apply or_intro1, or_intro1, P.
			- if QR; apply or_elim[OF QR];
				- if Q; apply or_intro1, or_intro2, Q.
				- if R; apply or_intro2, R.
				.
			.
		.
	- if [P : Prop, Q : Prop] then P ∨ Q ⟺ Q ∨ P;
		apply iff_intro;
		- if PQ; apply or.sym[OF PQ].
		- if QP; apply or.sym[OF QP].
		.
	- if QQ': Q ⟺ Q', [P : Prop, Q : Prop, Q' : Prop] then P ∨ Q ⟺ P ∨ Q';
		apply iff_intro;
		- if PQ; apply or_elim[OF PQ];
			- if P; apply or_intro1[OF P].
			- if Q; apply or_intro2[OF Q[unfold QQ']].
			.
		- if PQ'; apply or_elim[OF PQ'];
			- if P; apply or_intro1[OF P].
			- if Q'; apply or_intro2[OF Q'[fold QQ']].
			.
		.
	- if [P : Prop] then false ∨ P ⟺ P;
		apply iff_intro;
		- if fP; apply or_elim[OF fP]; by #elim false_elim.
		- if P; apply or_intro2[OF P].
		.
	- if [P : Prop] then true ∨ P ⟺ true;
		by iff_intro or_intro1.
	.

note#cong or.cong.
note#simp or.left_neutral or.right_neutral or.left_absorb or.right_absorb.

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
