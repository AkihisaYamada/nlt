import base? TypeFree.And.

begin

theory Iff :=
	fix (⟺).
	assume iff_eq_and: (P ⟺ Q) = ((P ⟹ Q) ∧ (Q ⟹ P)).
begin

	interpret! TypeFree.Iff;
		by #simp iff_eq_and.

	interpret And.

end
