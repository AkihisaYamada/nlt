import Imp, And, Or, Not, IntuitionisticNot, Iff.

begin

instance Minimal.

lemma not_intro! if P0: P ⟹ false, [P : Prop] then ¬P;
	apply imp_not_imp_not;
	- if P;
		use P0[OF P]; by #elim false_elim.
	.

lemma not_false: ¬false.

lemma not_false_iff#simp ¬false ⟷ true;
	apply iff_true.

lemma not_imp_false: if nP: ¬P, P: P, [P : Prop] then false;
	by not_elim[OF nP P].

lemma not_iff_imp_false: if [P : Prop] then ¬P ⟷ (P ⟶ false);
	apply iff_intro;
	- if nP; by not_imp_false[OF nP].
	- if P0; apply imp_not_imp_not;
		- if P; apply P0[THEN imp_elim1, OF P, THEN false_elim].
		.
	.

lemma not_imp_iff_false: if nP: ¬P, [P : Prop] then P ⟷ false;
	apply iff_intro;
	- if P; by not_imp_false[OF nP P].
	by #elim false_elim.

lemma iff_false_iff_not#simp if [P : Prop] then (P ⟷ false) ⟷ ¬P;
	apply iff_intro;
	- if P0; by #simp P0.
	by not_imp_iff_false.

lemma false_iff_iff_not#simp if [P : Prop] then (false ⟷ P) ⟷ ¬P;
	unfold[at 0] iff.commute;
	by iff_false_iff_not.

lemma and_simp1: if P: P, [P : Prop, Q : Prop] then P ∧ Q ⟷ Q;
	by iff_intro P.

lemma and_simp2: if Q: Q, [P : Prop, Q : Prop] then P ∧ Q ⟷ P;
	by iff_intro Q.

lemma or_simp1: if P: P, [P : Prop, Q : Prop] then P ∨ Q ⟷ true;
	simp iff_true[OF P].

lemma or_simp2: if Q: Q, [P : Prop, Q : Prop] then P ∨ Q ⟷ true;
	simp iff_true[OF Q].

instance and: iff.BooleanAlgebra (∧) (∨) false true;
	note! iff_intro or.left_assoc or.commute or.left_mono.
	- if [x : Prop] then x ∨ x ⟷ x; by or_intro1 #elim or_elim.
	- if [x : Prop, y : Prop, z : Prop] then x ∧ (y ∨ z) ⟷ x ∧ y ∨ x ∧ z;
		apply iff_intro;
		- if xyz; apply and_elim[OF xyz];
			- if x, yz; simp iff_true[OF x]; apply yz.
			.
		- if xyxz; apply or_elim[OF xyxz];
			- if xy; apply and_elim[OF xy];
				- if x, y; simp iff_true[OF x] iff_true[OF y].
				.
			- if xz; apply and_elim[OF xz];
				- if x, z; simp iff_true[OF x] iff_true[OF z].
				.
			.
		.
	- if [x : Prop, y : Prop] then x ∧ (x ∨ y) ⟷ x;
		apply iff_intro;
		- by #elim or_elim.
		- if x; simp iff_true[OF x].
		.
	- if [x : Prop, y : Prop, z : Prop] then x ∨ y ∧ z ⟷ (x ∨ y) ∧ (x ∨ z);
		apply iff_intro;
		- if xyz; apply or_elim[OF xyz];
			- if x; simp iff_true[OF x].
			- if yz; apply and_elim[OF yz];
				- if y, z; simp iff_true[OF y] iff_true[OF z].
				.
			.
		- if xyxz; apply and_elim[OF xyxz];
			- if xy, xz;
				apply or_elim[OF xy];
				- if x; simp iff_true[OF x].
				- if y; apply or_elim[OF xz];
					- if x; simp iff_true[OF x].
					- if z; simp iff_true[OF y] iff_true[OF z].
					.
				.
			.
		.
	- if [x : Prop, y : Prop] then x ∨ x ∧ y ⟷ x;
		apply iff_intro;
		- if xxy; apply or_elim[OF xxy].
		- if x; simp iff_true[OF x].
		.
	.

instance or: iff.BooleanAlgebra (∨) (∧) true false;
	by and.dual.left_distrib and.dual.left_absorptive and.dual.idem and.left_assoc and.commute and.left_mono and.idem and.left_distrib and.left_absorptive.

extend Membership begin

	extend Connex begin

		lemma not_imp_dual: if not: ¬ x ⊑ y, [x ∈ A, y ∈ A] then y ⊑ x;
			apply comparable[of x y, THEN or_elim];
			- if xy: x ⊑ y; apply not_elim[OF not xy].
			.

	end

end
