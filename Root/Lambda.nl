import Equal.

binder λ 0 0.

fix (λ).

assume beta: (λx. α.[x]) s = α.[s].

begin

setup rewrite eq_prop1 eq_prop2 eq.refl eq.trans.
setup dual eq.sym.

setup define beta.

theory Ext:
	assume ext: (∀x. α.[x] = β.[x]) ⟹ (λx. α.[x]) = (λx. β.[x]).
end
