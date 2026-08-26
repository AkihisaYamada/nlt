---
# Type-Free Equality
---
fix (=).

import eq: MetaReflexive (=).

assume eq_elim1: for P x y if x = y, P.[x] then P.[y].

begin

set simp (=).

---
## Theorems
---

note#intro#refl eq.refl.

---
Equality is an equivalence.
---
instance eq: MetaEquivalence (=);
	- if xy: x = y then y = x;
		by eq_elim1[of (z. z = x), OF xy].
	- if xy: x = y, yz: y = z then x = z;
		by eq_elim1[of (w. x = w), OF yz xy].
	.

note#dual eq.sym.
note#trans eq.trans.

lemma eq_elim2: for P if xy: x = y, Py: P.[y] then P.[x];
	by eq.sym[OF xy, THEN eq_elim1, OF Py].


lemma eq_imp#rewrite_imp if PQ: P = Q, P: P then Q;
	by eq_elim1[of (x. x), OF PQ P].

lemma eq_imp_rev#rewrite_rev if PQ: P = Q, Q: Q then P;
	by eq_imp[OF eq.sym[OF PQ] Q].

lemma eq_cong_meta: for X if yz: y = z then X.[y] = X.[z];
	by eq_elim1[of (w. X.[y] = X.[w]), OF yz eq.refl].

lemma unbind_cong: if XY: X = Y then X.[z] = Y.[z];
	by eq_cong_meta[of (X. X.[z]), OF XY].

lemma arg_cong: if xy: x = y then f x = f y;
	by eq_cong_meta[of (z. f z), OF xy].

lemma fun_cong: if fg: f = g then f x = g x;
	by eq_cong_meta[of (h. h x), OF fg].

lemma cong#cong? if fg: f = g, xy: x = y then f x = g y;
	.. = f y;
		by arg_cong[OF xy].
	by fun_cong[OF fg].

lemma eq_elim_dual: for P x y if xy: x = y, Py: P.[y] then P.[x];
	apply eq_elim1[OF eq.sym[OF xy] Py].

---
## Theories
---

theory MetaInjective f :=
	assume inj: if f x = f x' then x = x'.
end

theory MetaInverse f g :=
	assume inverse: g (f x) = x.
begin
	instance MetaInjective;
		- for x x' if eq: f x = f x' then x = x';
			.. = g (f x); unfold inverse.
			.. = g (f x'); unfold eq.
			unfold inverse.
		.
end

---
### Identity Combinator

The naive kernel does not even ensure the presence of a syntactic identity combinator.
Admitting one gives a convenient way of annotating terms.
---
theory Id :=
	fix id.
	assume id#simp id x = x.
end

theory Const :=-- aka K
	fix const.
	assume const#simp const x y = x.
end

theory Comp :=-- aka B
	fix (∘).
	assume o_app#simp (f ∘ g) x = f (g x).
begin

	definition comp2 = (∘) ∘ (∘).

	lemma comp2_app#simp comp2 f g x y = f (g x y);
		simp comp2_def.

	definition comp3 = comp2 ∘ (∘).

	lemma comp3#simp (comp3 f g x y z = f (g x y z));
		simp comp3_def.

end

theory Dual :=-- aka C
	fix dual.
	assume dual_app#simp dual f x y = f y x.
begin

	definition[as revimp] (⟸) = dual (⟹).
	lemma revimp_eq#simp (P ⟸ Q) = (Q ⟹ P);
		simp revimp_def.

end

theory AppBind :=
	fix _AppBind.
	assume _AppBind#simp _AppBind f (x. G.[x]) = (x. f G.[x]).
begin

end

theory BindComb :=
	fix _BindAppBind _BindConst.
	assume _BindAppBind#simp _BindAppBind (x. F.[x]) (x. G.[x]) = (x. F.[x] G.[x]).
	assume _BindConst#simp _BindConst s = (x. s).
begin

end

theory MetaIf :=
	fix If.
	assume If_then: if P then If P x y = x.
	---
	A paraconsistent specification: P and ¬P will not lead to explosion.
	---
	assume If_else: if P ⟹ x = y then If P x y = y.
begin
end

---
Extensionality
---
theory MetaExt :=
	assume bind_eq#cong if ∀x. F.[x] = G.[x] then (x. F.[x]) = (x. G.[x]).
end

extend Ex begin

	lemma ex_eq1: ∃x. x = a;
		apply ex_intro1[of a].

	lemma ex_eq2: ∃x. a = x;
		apply ex_intro1[of a].

end
