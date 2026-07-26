import And.
fix (⟺).
assume iff_eq_and: (P ⟺ Q) = ((P ⟹ Q) ∧ (Q ⟹ P)).

begin

interpret! Iff;
	by #simp iff_eq_and.

