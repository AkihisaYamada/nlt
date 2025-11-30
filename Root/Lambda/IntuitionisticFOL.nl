import Prop.
import TypedAll.

begin

define false := ∀P:prop. P.

interpret MinimalFOL;
	retain false;
		by #unfold false_def #elim all_elim.
	.

interpret ..IntuitionisticFOL;
	retain false;
		by #unfold false_def #elim all_elim.
	.

set rewrite iff_imp iff_imp_rev iff.refl iff.trans.
set dual iff.sym.


