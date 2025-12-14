------
# Untyped Lambda Calculus
------
import Eq.

fix (λ).

assume beta: (λx. α.[x]) s = α.[s].

begin

set define beta.

theory Ext:
	assume ext: if ∀x. α.[x] = β.[x] then (λx. α.[x]) = (λx. β.[x]).
end

theory Prop:
	import Prop.
	import Eq.
begin
	thy.
end
