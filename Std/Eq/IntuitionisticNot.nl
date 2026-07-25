interpret False.
import FalseNot.

begin

interpret ..Not, Not.IntuitionisticNot;
	- for P if nP: ¬P, P then Q;
		use nP[unfold not_eq_imp_false, OF P].
	.
