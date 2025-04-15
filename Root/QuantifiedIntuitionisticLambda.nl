import Lambda.
import TypedAll.
begin

setup rewrite eq_imp eq_imp_rev eq.refl eq.trans.
setup define beta.

define false := ∀P:prop. P.

interpret TypedFalse;
	by #unfold false_def #elim all_elim.

interpret QuantifiedMinimalLambda.

interpret QuantifiedIntuitionistic;
	retain false := false;
		by #unfold false_def #elim all_elim.
	.


