base Lambda.

import MinimalFOL.
import FunType.

begin

define choice_type ι := ∀P τ. (∀x:ι. ∃y:τ. P x y) ⟹ ∃f:ι→τ. ∀x:ι. P x (f x).

theory Choice:
	import ..Choice.
begin
	lemma choice_type: choice_type ι;
		unfold(=) choice_type_def;
		by choice.
end

