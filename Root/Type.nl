fix (→).
assume fun_type_elim1: (σ → τ) f ⟹ ∀a. σ a ⟹ τ (f a).
assume fun_type_intro! (∀a. σ a ⟹ τ (f a)) ⟹ (σ → τ) f.

begin

note fun_type_elim: make_elim[of (f. (σ → τ) f) (f. ∀a. σ a ⟹ τ (f a)), OF fun_type_elim1].



