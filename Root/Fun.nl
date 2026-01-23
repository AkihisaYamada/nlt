import Membership.

fix (→).
assume fun_intro: for f if ∀a. a ∈ A ⟹ f a ∈ B then f ∈ A → B.
assume fun_elim1: if f ∈ A → B, a ∈ A then f a ∈ B.

begin

