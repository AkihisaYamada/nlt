base Equal.

binder λ 0 0.

fix (λ).

assume beta: (λx. α.[x]) s = α.[s].

begin

setup define beta.

theory Ext:
	assume ext: (∀x. α.[x] = β.[x]) ⟹ (λx. α.[x]) = (λx. β.[x]).
end
