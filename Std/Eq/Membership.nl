import Std.Membership.

begin

theory Antisymmetric A (⊑) :=
	assume antisym: if x ⊑ y, y ⊑ x, x ∈ A, y ∈ A then x = y.
begin
	interpret Attractive A (⊑);
		- if xy: x ⊑ y, yx: y ⊑ x; by #simp antisym[OF xy yx].
		- if xy: x ⊑ y, yx: y ⊑ x; by #simp antisym[OF yx xy].
		.
end

theory PseudoOrder :=
	import Reflexive, Antisymmetric.
end

theory Order :=
	import Preorder, Antisymmetric.
begin
	interpret PseudoOrder.
end

theory Injective f A :=
	assume injective: if x ∈ A, x' ∈ A, f x = f x' then x = x'.
end

theory Inverse f A g :=
	assume inverse: if x ∈ A then g (f x) = x.
end

theory Abbrev :=
	assume abbrev: for F if ∀f. (∀A x. F.[x] ∈ A ⟹ f x = F.[x]) ⟹ P then P.
begin

end

theory Pair :=
	fix (,) fst snd.
	assume fst_pair: if x ∈ A, y ∈ B then fst (x,y) = x.
	assume snd_pair: if x ∈ A, y ∈ B then snd (x,y) = y.
end
