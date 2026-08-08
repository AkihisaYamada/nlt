import base? Std.Membership.

begin

theory Antisymmetric A (⊑) :=
	assume antisym: if x ⊑ y, y ⊑ x, x ∈ A, y ∈ A then x = y.
begin
	instance Attractive A (⊑);
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
	instance PseudoOrder.
end

theory Injective f A :=
	assume injective: if x ∈ A, x' ∈ A, f x = f x' then x = x'.
end

theory Inverse f A g :=
	assume inverse: if x ∈ A then g (f x) = x.
end

theory Prod :=
	fix (,) fst snd.
	assume fst_pair: if x ∈ A, y ∈ B then fst (x,y) = x.
	assume snd_pair: if x ∈ A, y ∈ B then snd (x,y) = y.
end

theory Abbrev :=
	assume abbrev: for F if ∀f. (∀A x. F.[x] ∈ A ⟹ f x = F.[x]) ⟹ P then P.
end

theory Fun :=
	fix (fun).
	assume fun_app: -- @aka β reduction
		for A F if F.[s] ∈ A then (fun x. F.[x]) s = F.[s].
begin

	instance base.Fun;
		- for P A if P: P.[(fun x. F.[x]) s], FsA: F.[s] ∈ A then P.[F.[s]];
			use P[unfold fun_app[OF FsA]].
		.

	---
	If the result is a member, then function application can be reduced.
	---
	lemma fun_app_eq: for A if eq: F.[s] = t, ! t ∈ A then (fun x. F.[x]) s = t;
		.. = F.[s];
			apply fun_app[of A];
			by #simp eq.
		by #simp eq.

	lemma fun_indep#simp[after 1] if ! s ∈ A then (fun x. s) t = s;
		by fun_app[of A].

	instance Abbrev;
		- if assm: ∀f. (∀A x. F.[x] ∈ A ⟹ f x = F.[x]) ⟹ P then P;
			apply assm[of (fun x. F.[x])];
			by #elim fun_app.
		.

end