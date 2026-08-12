import base? Std.Membership.

begin

theory Antisymmetric A (⊑) :=
	assume antisym: if x ⊑ y, y ⊑ x, x ∈ A, y ∈ A then x = y.
begin
	instance Attractive A (⊑);
		- if xy: x ⊑ y, yx: y ⊑ x, ...; by #simp antisym[OF xy yx].
		- if xy: x ⊑ y, yx: y ⊑ x, ...; by #simp antisym[OF yx xy].
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

theory FunIn :=
	fix (fun_∈).
	assume funIn_app#simp if s ∈ A then (fun x ∈ A. F.[x]) s = F.[s].
begin

	instance base.FunIn;
		note#cong eq_cong_meta.
		- for P A F s if P, sA; use sA P.-- the order of assumptions matters.
		.

end

theory FunTo :=
	import FunIn, base.FunTo.
end

theory PolyFun :=
	fix (fun).
	assume fun_app_poly: -- @aka β reduction
		for A F if s ∈ A then (fun x. F.[x]) s = F.[s].
begin

	instance base.PolyFun;
		note#cong eq_cong_meta.
		- for P A if P: P.[(fun x. F.[x]) s], sA: s ∈ A then P.[F.[s]];
			use P[unfold fun_app_poly[OF sA]].
		.

end