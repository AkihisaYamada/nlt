import Equal.


fix (λ).

assume beta: (λx. α.[x]) s = α.[s].

begin

setup rewrite eq_imp eq_imp_rev eq.refl eq.trans.
setup dual eq.sym.

setup define beta.

theory Ext:
	assume ext: (∀x. α.[x] = β.[x]) ⟹ (λx. α.[x]) = (λx. β.[x]).
end

define [fun] (σ → τ) f := ∀x. σ x ⟹ τ (f x).

interpret FunType;
	instantiate (→) := (→).
	- for σ τ f, if f: (σ → τ) f then ∀a. σ a ⟹ τ (f a);
		apply f[unfolded fun_def]!0.
	- for σ τ f, if assm: ∀x. σ x ⟹ τ (f x) then (σ → τ) f;
		unfold fun_def;
		apply assm!0.
	.


