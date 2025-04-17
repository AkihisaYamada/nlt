import MinimalFOL.
import FunType.

begin

theory ChoiceType:
	fix ι.
	assume choice: (∀x:ι. ∃y:τ. P x y) ⟹ ∃f:ι→τ. ∀x:ι. P x (f x).
end

theory Choice:
	assume choice: (∀x:ι. ∃y:τ. P x y) ⟹ ∃f:ι→τ. ∀x:ι. P x (f x).
end


