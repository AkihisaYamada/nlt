fix (∈) PROP TYPE (→).

assume PROP_TYPE! PROP ∈ TYPE.
assume FUN_TYPE! if A ∈ TYPE, B ∈ TYPE then A → B ∈ TYPE.
import FOL.
import Fun.

begin

theory Choice:
	fix CHOICE.
	assume choice:
	if ∀x ∈ A. ∃y ∈ B. P x y, A ∈ TYPE, B ∈ CHOICE
	then ∃f ∈ A → B. ∀x ∈ A. P x (f x).
end