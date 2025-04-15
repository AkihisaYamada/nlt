base Lambda.
import TypedAll.

begin

define false := ∀P:prop. P.

interpret TypedFalse;
	by #unfold false_def #elim all_elim.

interpret QuantifiedMinimal.

interpret ..QuantifiedIntuitionistic;
	retain false := false;
		by #unfold false_def #elim all_elim.
	.


