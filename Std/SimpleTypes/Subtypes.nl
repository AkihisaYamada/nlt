assume Subtype: for p if ∀Subtype.
		(∀V. Subtype : TYPE V → TYPE V) ⟹
		(∀A x. x : A ⟹ p x ⟹ x : Subtype A) ⟹
		(∀A x. x : Subtype A ⟹ p x) ⟹
		(∀A x. x : Subtype A ⟹ x : A) ⟹ thesis
	then thesis.

begin


