------
# Type-Free Lambda Calculus
------
import Eq.

fix (λ).

assume beta: (λx. Y.[x]) s = Y.[s].

begin

set define beta.

theory Ext:
	assume ext: if ∀x. Y.[x] = Z.[x] then (λx. Y.[x]) = (λx. Z.[x]).
end

theory If:
	import If.
begin
	interpret Pair;
		define[pair] (x,y) P := (If P x y).
		define fst xy := xy (∀P. P ⟹ P).
		define snd xy := xy (∀P. P).
	- for x y, fst (x,y) = x;
		by If_then #unfold fst_def pair_def.
	- for x y, snd (x,y) = y;
		by If_else #unfold snd_def pair_def.
	.
end

