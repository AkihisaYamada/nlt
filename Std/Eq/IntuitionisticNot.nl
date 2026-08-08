instance False.
import FalseNot.

begin

instance Std.Not, Not.IntuitionisticNot;
	- for P if nP: ¬P, P then Q;
		use nP[unfold not_eq_imp_false, OF P].
	.
