import Std.Membership.

begin

theory Antisymmetric A (⊑) :=
	assume antisym: if x ⊑ y, y ⊑ x, x ∈ A, y ∈ A then x = y.
begin
	interpret Attractive A (⊑);
		- by #simp[after 2] antisym.
		- by #simp[after 2] antisym[OF _ <].
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

	obtain id where id_app#simp[after 1] if a ∈ A then id a = a;
		- for thesis if assm;
			apply abbrev[of (x. x)];
			- for id if id;
				apply assm[OF id].
			.
		.

end

theory Pair :=
	fix (,) fst snd.
	assume fst_pair: if x ∈ A, y ∈ B then fst (x,y) = x.
	assume snd_pair: if x ∈ A, y ∈ B then snd (x,y) = y.
end
