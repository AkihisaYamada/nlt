base Lambda.

import MinimalFOL.
import FunType.

begin

import ..MinimalHOL.

setup rewrite iff_imp iff_imp_rev iff.refl iff.trans.
setup dual iff.sym.

define choice_type ι := ∀P τ. (∀x:ι. ∃y:τ. P x y) ⟹ ∃f:ι→τ. ∀x:ι. P x (f x).

theory Choice:
	import ..Choice.
begin
	lemma choice_type: choice_type ι;
		unfold(=) choice_type_def;
		by choice.
end

