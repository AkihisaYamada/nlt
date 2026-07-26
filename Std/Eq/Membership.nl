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

theory Fun :=
	fix (fun).
	assume fun_app: for A F if F.[x] ∈ A then (fun x. F.[x]) x = F.[x].
begin

	interpret Abbrev;
		- if assm: ∀f. (∀A x. F.[x] ∈ A ⟹ f x = F.[x]) ⟹ P then P;
			apply assm[of (fun x. F.[x])];
			by #elim fun_app.
		.

	theory FunType :=
		fix (FUN).
		assume fun_FUN#intro if ∀x. F.[x] ∈ A.[x] then (fun x. F.[x]) ∈ FUN x. A.[x].
	begin

		define const = fun x y. x.

		lemma const_app: if xA: x ∈ A then const x y = x;
			unfold const_def;
			apply fun_app[of (FUN x. A), THEN eq_elim_dual[of (z. z y = x)]];
			by xA #simp fun_app[OF xA].

	end

end


theory Pair :=
	fix (,) fst snd.
	assume fst: if x ∈ A, y ∈ B then fst (x,y) = x.
	assume snd: if x ∈ A, y ∈ B then snd (x,y) = y.
end

