interpret False.
import FalseNot.

begin

interpret Not.IntuitionisticNot;
	by #simp not_iff_imp_false false_iff.

interpret MinimalNot.

context Not.IntuitionisticNot begin

	extend Iff begin

		interpret False.
		interpret Iff.IntuitionisticNot;
			- for P;
				apply iff_intro;
				- by #elim not_elim.
				- if P0; by not_intro #elim P0.
				.
			.

	end

end
