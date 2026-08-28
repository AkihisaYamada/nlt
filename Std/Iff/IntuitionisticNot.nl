import Not.
assume not_iff_imp_false: ¬P ⟺ (P ⟹ false).

begin

instance Not.IntuitionisticNot;
	- by #simp not_iff_imp_false.
	- if nP: ¬P, P: P then Q;
		use nP[unfold not_iff_imp_false, OF P].
	.

instance MinimalNot.

context Not.IntuitionisticNot begin

	extend Iff begin

		instance False.
		instance Iff.IntuitionisticNot;
			- for P;
				apply iff_intro;
				- by #elim not_elim.
				- if P0; by not_intro #elim P0.
				.
			.

	end

end
