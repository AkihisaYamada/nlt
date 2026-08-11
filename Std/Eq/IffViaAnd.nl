import And.
fix (⟺).
assume iff_eq_and: (P ⟺ Q) = ((P ⟹ Q) ∧ (Q ⟹ P)).

begin

instance! Iff;
	by #simp iff_eq_and.

