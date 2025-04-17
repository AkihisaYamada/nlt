base Lambda.
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

setup rewrite iff_imp iff_imp_rev iff.refl iff.trans.
setup dual iff.sym.


