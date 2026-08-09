import False, And, Or, Not, IntuitionisticNot, Iff.

begin

instance Minimal.

lemma not_intro! if P0: P ⟹ false, [P : Prop] then ¬P;
	apply imp_not_imp_not;
	- if P;
		use P0[OF P]; by #elim false_elim.
	.
