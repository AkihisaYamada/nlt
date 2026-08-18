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
	assume injective: if f x = f x', x ∈ A, x' ∈ A then x = x'.
end

theory Inversive f A g :=
	assume inverse: if x ∈ A then g (f x) = x.
begin

	instance Injective f A;
		- if eq: f x = f x', ... then x = x';
			.. = g (f x); by #simp inverse.
			.. = g (f x'); by #simp eq.
			by #simp inverse.
		.

end

---
## Additional Postulates
---

theory Image :=
	fix (`).
	assume app_in_image: if x ∈ A then f x ∈ f ` A.
	assume image_elim: if y ∈ f ` A, ∀x. y = f x ⟹ x ∈ A ⟹ P then P.
begin

	lemma image_intro1: for x if y: y = f x, x: x ∈ A then y ∈ f ` A;
		unfold y; apply app_in_image, x.

	lemma image_intro: if assm: ∀P. (∀x. y = f x ⟹ x ∈ A ⟹ P) ⟹ P then y ∈ f ` A;
		apply assm;
		- for x; by image_intro1[of x].
		.
		

end

theory Prod :=
	import Pair.
	fix (×).
	assume prod_intro1! if x ∈ A, y ∈ B then (x,y) ∈ A × B.
	assume prod_pair_elim: for P if p ∈ A × B, ∀x. x ∈ A ⟹ ∀y. y ∈ B ⟹ P.[(x,y)] then P.[p].
begin

	lemma prod_cases: if p: p ∈ A × B, assm: ∀x y. p = (x,y) ⟹ x ∈ A ⟹ y ∈ B ⟹ P then P;
		use eq.refl[of p];
		apply prod_pair_elim[of (q. p = q ⟹ P), OF p]>1;
		- if [x ∈ A, y ∈ B], p: p = (x,y);
			by assm[OF p].
		.

	lemma prod_exhaust: if p: p ∈ A × B then (fst p, snd p) = p;
		apply prod_cases[OF p];
		- if p: p = (x,y), ...;
			simp p.
		.
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
begin

	theory Ext :=
		assume ext: if ∀x. x ∈ A ⟹ f x = g x, f ∈ A → B, g ∈ A → B then f = g.
	end

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