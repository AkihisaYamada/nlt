---
# Type-Free Equality
---
fix (=).

import eq: MetaReflexive (=).

assume eq_elim: for P x y if x = y, P.[x] then P.[y].

begin

set simp (=).

---
## Theorems
---

note#intro#refl eq.refl.

---
Equality is an equivalence.
---
interpretation eq: MetaEquivalence (=);
	- if xy: x = y then y = x;
		by eq_elim[of (z. z = x), OF xy].
	- if xy: x = y, yz: y = z then x = z;
		by eq_elim[of (w. x = w), OF yz xy].
	.

note#dual eq.sym.
note#trans eq.trans.

lemma eq_imp#rewrite_imp if PQ: P = Q, P: P then Q;
	by eq_elim[of (x. x), OF PQ P].

lemma eq_imp_rev#rewrite_rev if PQ: P = Q, Q: Q then P;
	by eq_imp[OF eq.sym[OF PQ] Q].

lemma eq_cong_meta#cong for X if yz: y = z then X.[y] = X.[z];
	by eq_elim[of (w. X.[y] = X.[w]), OF yz eq.refl].

lemma unbind_cong: if XY: X = Y then X.[z] = Y.[z];
	by eq_cong_meta[of (X. X.[z]), OF XY].

lemma arg_cong: if xy: x = y then f x = f y;
	by eq_cong_meta[of (z. f z), OF xy].

lemma fun_cong: if fg: f = g then f x = g x;
	by eq_cong_meta[of (h. h x), OF fg].

lemma cong#cong? if fg: f = g, xy: x = y then f x = g y;
	... = f y;
		by arg_cong[OF xy].
	by fun_cong[OF fg].

lemma eq_elim_dual: for P x y if xy: x = y, Py: P.[y] then P.[x];
	apply eq_elim[OF eq.sym[OF xy] Py].

---
## Theories
---

theory MetaInjective f :=
	assume inj: if f x = f x' then x = x'.
end

theory MetaInverse f g :=
	assume inverse: g (f x) = x.
begin
	interpretation MetaInjective;
		- for x x' if eq: f x = f x' then x = x';
			... = g (f x); unfold inverse.
			... = g (f x'); unfold eq.
			unfold inverse.
		.
end

theory Id :=
	fix id.
	assume id#simp id x = x.
begin
	
end

theory Const :=-- aka K
	fix const.
	assume const#simp const x y = x.
end

theory Comp :=-- aka B
	fix (∘).
	assume comp_app#simp (f ∘ g) x = f (g x).
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

end

theory Comb :=
	import Id, Const, Comp, Dual.
begin

	definition app = (∘) id.
	lemma app#simp app f x = f x;
		simp app_def.

	definition paracomp = dual ((∘) ∘ dual (∘)).
	lemma paracomp_app#simp paracomp f g x y = f x (g y);
		simp paracomp_def.

	definition[as revapp] (|>) = dual id.
	lemma revapp#simp x |> f = f x;
		simp revapp_def.

	lemma : ((z |>) ∘ (y |>) ∘ (x |>)) f = f x y z.

	obtain pair_tp where pair_tp_spec:
		if	pair = pair_tp (const ∘ dual const),
			fst = pair_tp (const const),
			snd = pair_tp (const ∘ const),
			(∀x y. fst (pair x y) = x) ⟹
			(∀x y. snd (pair x y) = y) ⟹ P
		then P;
		- for thesis if assm;
			apply assm[of ((dual ((∘) ∘ dual ∘ dual id) id |>) ∘ ((const |>) |>) ∘ ((dual const |>) |>))];
			- for pair if pair0 for fst if fst0 for snd if snd0 for P if assm2;
				apply assm2;
				- for x y; simp fst0 pair0.
				- for x y; simp snd0 pair0.
				.
			.
		.

	definition[as pair] (,) = pair_tp (const ∘ dual const).
	definition fst = pair_tp (const const).
	definition snd = pair_tp (const ∘ const).

	lemma fst_pair#simp fst (x,y) = x;
		apply pair_tp_spec[OF pair_def fst_def snd_def].

	lemma snd_pair#simp snd (x,y) = y;
		apply pair_tp_spec[OF pair_def fst_def snd_def].


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
theory Ext :=
	assume bind_eq#cong if ∀x. F.[x] = G.[x] then (x. F.[x]) = (x. G.[x]).
end

extend Ex begin

	lemma ex_eq1: ∃x. x = a;
		apply ex_intro1[of a].

	lemma ex_eq2: ∃x. a = x;
		apply ex_intro1[of a].

end
