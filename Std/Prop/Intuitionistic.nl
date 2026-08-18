import False, And, Or, Not, IntuitionisticNot, Iff.

begin

instance Minimal.

lemma not_intro! if P0: P ⟹ false, [P : Prop] then ¬P;
	apply imp_not_imp_not;
	- if P;
		use P0[OF P]; by #elim false_elim.
	.

lemma not_false: ¬false.

lemma not_false_iff#simp ¬false ⟺ true;
	apply iff_true.

lemma not_imp_false: if nP: ¬P, P: P, [P : Prop] then false;
	by not_elim[OF nP P].

lemma not_iff_imp_false: if [P : Prop] then ¬P ⟺ (P ⟹ false);
	apply iff_intro;
	- if nP, P; by not_imp_false[OF nP P].
	- if P0; apply imp_not_imp_not;
		- if P; apply false_elim[OF P0[OF P]].
		.
	.

lemma not_imp_iff_false: if nP: ¬P, [P : Prop] then P ⟺ false;
	apply iff_intro;
	- if P; by not_imp_false[OF nP P].
	by #elim false_elim.

lemma iff_false_iff_not#simp if [P : Prop] then (P ⟺ false) ⟺ ¬P;
	apply iff_intro;
	- if P0; by #simp P0.
	by not_imp_iff_false.

lemma false_iff_iff_not#simp if [P : Prop] then (false ⟺ P) ⟺ ¬P;
	unfold[at 0] iff.commute;
	by iff_false_iff_not.

instance ExplosiveNot.False.



extend Membership begin

	extend Connex begin

		lemma not_imp_dual: if not: ¬ x ⊑ y, [x ∈ A, y ∈ A] then y ⊑ x;
			apply comparable[of x y, THEN or_elim];
			- if xy: x ⊑ y; apply not_elim[OF not xy].
			.

	end

end
