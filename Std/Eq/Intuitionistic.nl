define false = (∀P. P).
import Minimal.
begin

interpret TypeFree.Intuitionistic;
	by #simp false_def.

end