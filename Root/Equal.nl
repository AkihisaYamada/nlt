---
# Equality
---

import Base.

fix (=).

import eq: MetaReflexive (=).

assume eq_imp_meta: for X, if y = z, X.[y] then X.[z].

begin -- Above are the all axioms.

note! eq.refl.

interpret eq: MetaSymmetric (=);
	- for x y if xy: x = y then y = x;
		by eq_imp_meta[of (z. z = x), OF xy eq.refl].
	.

interpret eq: MetaTransitive (=);
	- for x y z if xy: x = y, yz: y = z then x = z;
		by eq_imp_meta[of (w. x = w), OF yz xy].
	.

interpret eq: MetaEquivalence (=).

lemma eq_imp: if PQ: P = Q, P: P then Q;
	by eq_imp_meta[of (x. x), OF PQ P].

lemma eq_imp_rev: if PQ: P = Q, Q: Q then P;
	by eq_imp[OF eq.sym[OF PQ] Q].

set rewrite eq_imp eq_imp_rev eq.refl eq.trans.
set dual eq.sym.

lemma eq_cong_meta: for α if xy: x = y then α.[x] = α.[y];
	by eq_imp_meta[of (z. α.[x] = α.[z]), OF xy eq.refl].

lemma arg_cong: if xy: x = y then f x = f y;
	by eq_cong_meta[of (z. f z), OF xy].

lemma fun_cong: if fg: f = g then f x = g x;
	by eq_cong_meta[of (h. h x), OF fg].

lemma eq_cong#cong: for f x if fg: f = g, xy: x = y then f x = g y;
	have 1: f x = f y;
		by arg_cong[OF xy].
	have 2: f y = g y;
		by fun_cong[OF fg].
	by eq.trans[OF 1 2].

theory Const:
	fix Const const const_fun const_arg.
	assume const_Const: const Const.
	assume const_app: if const c then const (c x).
	assume const_fun: if const c then const_fun (c x) = c.
	assume const_arg: if const c then const_arg (c x) = x.
begin
	lemma const_eq_fun: if ! const c, ! const d, cd: c x = d y then c = d;
		have 1: const_fun (c x) = const_fun (d y);
			unfold cd.
		by 1[unfolded+ const_fun].
	lemma const_eq_arg: if ! const c, ! const d, cd: c x = d y then x = y;
		have 1: const_arg (c x) = const_arg (d y);
			unfold cd.
		by 1[unfolded+ const_arg].
end


theory TwoValued:
	assume imp_imp_eq: if P, Q then P = Q.
	assume imp_eq: if P then (P ⟹ Q) = Q.
begin
	obtain true where true_intro: true;
		- for thesis if assm;
			apply assm[of (∀P. P ⟹ P)].
		.
	lemma eq_true: if P: P then P = true;
		by imp_imp_eq[OF P true_intro].
	lemma true_eq: if P: P then true = P;
		unfold eq_true[OF P].
	lemma eq_refl_eq_true: (x = x) = true;
		by eq_true[OF eq.refl].
	lemma weaken_eq: (P ⟹ Q ⟹ P) = true;
		by eq_true[OF weaken].
	lemma imp_true_eq: (P ⟹ true) = true;
		by eq_true[OF weaken[OF true_intro]].
	lemma true_imp_eq: (true ⟹ P) = P;
		by imp_eq[OF true_intro].
	interpret imp: MetaLeftNeutral (⟹) true (=);
		- for P;
			apply+ imp_eq true_intro.
		.
	interpret imp: MetaRightAbsorb (⟹) true (=);
		- for P;
			by eq_true true_intro.
		.
	end
end

theory Prop:
	import ..Prop.
begin
	theory EqType:
		fix ι.
		import eq: Relation ι (=).
	end
end

theory MetaInjective:
	fix f.
	assume inj: if f x = f x' then x = x'.
end

theory MetaInverse:
	fix f f⁻.
	assume inverse: f⁻ (f x) = x.
begin
	interpret MetaInjective;
		- for x x' if eq: f x = f x';
			have 1: f⁻ (f x) = f⁻ (f x');
				unfold eq.
			by 1[unfolded inverse].
		.
end

theory Pair:
	fix Pair fst snd.
	assume fst: fst (Pair x y) = x.
	assume snd: snd (Pair x y) = y.
begin
	interpret Pair: MetaInjective Pair;
		- for x x', if eq: Pair x = Pair x' then x = x';
			have 1: fst (Pair x x) = fst (Pair x' x);
				unfold eq.
			by 1[unfolded fst].
		.
end
