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

end

theory Pair :=
	fix (,) fst snd.
	assume fst_pair: if x ∈ A, y ∈ B then fst (x,y) = x.
	assume snd_pair: if x ∈ A, y ∈ B then snd (x,y) = y.
end

theory Fun :=
	fix (fun).
	assume fun_app: -- @aka β reduction
		for A F if F.[s] ∈ A then (fun x. F.[x]) s = F.[s].
begin

	---
	If the result is typed, then function application can be reduced.
	---
	lemma fun_app_eq: for A if eq: F.[s] = t, [t ∈ A] then (fun x. F.[x]) s = t;
		... = F.[s];
			apply fun_app[of A];
			by #simp eq.
		... = t;
			by #simp eq.
		.

	lemma in_fun_app_eq: for A if t: t ∈ A, eq: F.[s] = t then (fun x. F.[x]) s = t;
		apply fun_app_eq[OF eq t].

	lemma fun_indep: for A if s: s ∈ A then (fun x. s) t = s;
		apply fun_app[OF s].

	interpret Abbrev;
		- if assm: ∀f. (∀A x. F.[x] ∈ A ⟹ f x = F.[x]) ⟹ P then P;
			apply assm[of (fun x. F.[x])];
			by #elim fun_app.
		.

end