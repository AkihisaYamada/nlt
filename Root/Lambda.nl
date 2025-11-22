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

define [type] x : σ := σ x.
define [fun] (σ → τ) f := ∀x. x : σ ⟹ f x : τ.

interpret FunType;
	- for f σ τ, if f: f : σ → τ then ∀a. a : σ ⟹ f a : τ;
		apply f[unfolded+ type_def fun_def]!0.
	- for f σ τ, if assm: ∀x. x : σ ⟹ f x : τ then f : σ → τ;
		unfold+ type_def fun_def;
		apply assm!0.
	.


