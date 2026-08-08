instance False.
import FalseNot.

begin

instance Not.IntuitionisticNot;
	by #simp not_iff_imp_false false_iff.

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
