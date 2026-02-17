---
# Equality
---

interpret Base.

fix (=).

import eq: MetaReflexive (=).

assume eq_elim: for X y z if y = z, X.[y] then X.[z].

begin
---
## Theorems
---

note! eq.refl.

---
Equality is an equivalence.
---
interpret eq: MetaEquivalence (=);
	- if xy: x = y then y = x;
		by eq_elim[of (z. z = x), OF xy].
	- if xy: x = y, yz: y = z then x = z;
		by eq_elim[of (w. x = w), OF yz xy].
	.

lemma eq_cong_meta: for X if yz: y = z then X.[y] = X.[z];
	by eq_elim[of (w. X.[y] = X.[w]), OF yz eq.refl].

lemma eq_imp: if PQ: P = Q, P: P then Q;
	by eq_elim[of (x. x), OF PQ P].

lemma eq_imp_rev: if PQ: P = Q, Q: Q then P;
	by eq_imp[OF eq.sym[OF PQ] Q].

set rewrite eq_imp eq_imp_rev eq.refl eq.trans.
set dual eq.sym.

lemma arg_cong: if xy: x = y then f x = f y;
	by eq_cong_meta[of (z. f z), OF xy].

lemma fun_cong: if fg: f = g then f x = g x;
	by eq_cong_meta[of (h. h x), OF fg].

lemma cong(fallback) if fg: f = g, xy: x = y then f x = g y;
	have 1: f x = f y;
		by arg_cong[OF xy].
	apply eq.trans[OF 1];
	by fun_cong[OF fg].

---
## Theories
---

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
		by eq_true.
	lemma weaken_eq: (P ⟹ Q ⟹ P) = true;
		by eq_true.
	lemma imp_true_eq: (P ⟹ true) = true;
		by eq_true true_intro.
	lemma true_imp_eq: (true ⟹ P) = P;
		by imp_eq[OF true_intro].
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
			by 1[unfold inverse].
		.
end

theory If:
	fix If.
	assume If_then: for P x y if P then If P x y = x.
	---
	A minimal specification: P and ¬P will not lead to explosion.
	---
	assume If_else: if P ⟹ x = y then If P x y = y.
begin
end

theory Pair: --- Syntactic Pairing ---
	fix (,) fst snd.
	assume fst(simp) fst (x,y) = x.
	assume snd(simp) snd (x,y) = y.
begin
	interpret pair: MetaInjective (,);
		- for x x' if eq: (,) x = (,) x' then x = x';
			have 1: fst (x,x) = fst (x',x);
				unfold eq.
			by 1[unfold fst].
		.
	lemma pair_eq_pair_intro: if x: x = x', y: y = y' then (x,y) = (x',y');
		simp x y.
	lemma pair_eq_pair_elim1: if eq: (x,y) = (x',y') then x = x';
		have 1: x = fst (x,y).
		apply eq.trans[OF 1];
		have 2: fst (x,y) = fst (x',y');
			unfold eq.
		apply eq.trans[OF 2];
		have 3: fst (x',y') = x';
			unfold fst.
		by eq.trans[OF 3].

	lemma pair_eq_pair_elim2: if eq: (x,y) = (x',y') then y = y';
		have 1: y = snd (x,y);
			unfold snd.
		apply eq.trans[OF 1];
		have 2: snd (x,y) = snd (x',y');
			unfold eq.
		apply eq.trans[OF 2];
		have 3: snd (x',y') = y';
			unfold snd.
		by eq.trans[OF 3].

end

theory Membership:
	import Membership.
begin

	interpret Magmas.

	theory Antisymmetric:
		fix A (≤).
		assume antisym: if x ≤ y, y ≤ x, x ∈ A, y ∈ A then x = y.
	begin
		interpret Attractive;
			- if xy: x ≤ y, yx: y ≤ x, yz: y ≤ z, x: x ∈ A, y: y ∈ A, z: z ∈ A then x ≤ z;
				unfold antisym[OF xy yx x y];
				by yz.
			- if xy: x ≤ y, yx: y ≤ x, xz: x ≤ z, x: x ∈ A, y: y ∈ A, z: z ∈ A then y ≤ z;
				unfold antisym[OF yx xy y x];
				by xz.
			.
	end

	theory PseudoOrder:
		import Reflexive.
		import Antisymmetric.
	end

	theory Order:
		import Preorder.
		import Antisymmetric.
	begin
		interpret PseudoOrder.
	end

end

theory TypeSafeMinimal:
	import TypeSafeMinimal.
begin

	lemma eq_refl_iff(simp) x = x ⟺ true;
		by iff_intro.

	interpret iff_eq: iff.MetaCommutative (=);
		by iff_intro[OF eq.sym eq.sym].

	lemma eq_imp_iff(fallback) if eq: P = Q then P ⟺ Q;
		unfold[on (=)] eq.

	lemma all_eq_imp_iff: (∀x. x = a ⟹ P.[x]) ⟺ P.[a];
		apply iff_intro;
		- if all;
			apply all.
		- if Pa: P.[a], xa: x = a;
			note(cong) eq_cong_meta[of P].
			by Pa #unfold xa.
		.

	theory AllRel:
		import AllRel.
	begin
		lemma all_cong:
			if ab: a = b, PQ: ∀x. x < b ⟹ P.[x] ⟺ Q.[x]
			then (∀x < a. P.[x]) ⟺ (∀x < b. Q.[x]);
			apply iff_intro;
			- if Pa;
				apply all_intro;
				by all_elim1[OF Pa, unfold ab] #fold PQ.
			- if Qb;
				apply all_intro;
				by all_elim1[OF Qb] #unfold ab PQ.
			.
		lemma all_eq_imp_iff: (∀x < a. x = b ⟹ P.[x]) ⟺ (b < a ⟹ P.[b]);
			have 1: (∀x < a. x = b ⟹ P.[x]) ⟺ (∀x. x = b ⟹ x < a ⟹ P.[x]);
				unfold all_def;
				by iff_intro.
			unfold 1;
			unfold all_eq_imp_iff.
	end

	theory Pair:
		import Pair.
	begin
		lemma pair_eq_pair(simp) (x,y) = (x',y') ⟺ x = x' ∧ y = y';
			apply iff_intro;
			- if eq;
				by pair_eq_pair_elim1[OF eq] pair_eq_pair_elim2[OF eq].
			simp;
			- if x, y;
				simp x y.
			.
	end

	theory Ex1:
		fix (∃!).
		assume ex1_def: (∃!x. P.[x]) = (∃x. P.[x] ∧ (∀y. P.[y] ⟹ y = x)).
	begin
		lemma ex1_intro1: for x P if Px: P.[x], u: ∀y. P.[y] ⟹ y = x then ∃!x. P.[x];
			unfold ex1_def;
			by ex_intro1[of x] Px u.
		lemma ex1_intro: if assm: ∀Q. (∀x. P.[x] ⟹ (∀y. P.[y] ⟹ y = x) ⟹ Q) ⟹ Q then ∃!x. P.[x];
			apply assm;
			- for x if Px;
				by ex1_intro1[OF Px].
			.
	end

	theory The:
		import Ex1.
		fix (THE).
		assume ex1_imp_THE: (∃!x. P.[x]) ⟹ P.[THE x. P.[x]].
	end

	theory UniqueChoice:
		import Ex1.
		import Pair.
		assume unique_choice: if ∀x. ∃!y. P.[x,y] then ∃f. ∀x. P.[x, f x].
	end

end

interpret TypeFree.

theory Minimal:
	import TypeFree? Minimal.
begin

	interpret local? TypeSafeMinimal.

	lemma ex_eq_and_iff: (∃x. x = a ∧ P.[x]) ⟺ P.[a];
		apply iff_intro;
		simp;
		note(cong) eq_cong_meta[of P].
		- if xa: x = a, Px: P.[x];
			by Px #fold xa.
		- if Pa: P.[a];
			by ex_intro1[of a] Pa.
		.

	theory Ex1:
		import Ex1.
	begin
		lemma ex1_cong_iff(cong)
			if iff: ∀x. P.[x] ⟺ P'.[x] then (∃!x. P.[x]) ⟺ (∃!x. P'.[x]);
			unfold ex1_def iff.
		lemma ex1_elim: if ex1: ∃!x. P.[x], all: ∀x. P.[x] ⟹ (∀y. P.[y] ⟹ y = x) ⟹ Q then Q;
			apply ex1[unfold ex1_def, THEN ex_elim];
			- for x;
				by all[of x].
			.
		lemma ex1_imp_ex: if ex1: ∃!x. P.[x] then ∃x. P.[x];
			apply ex1_elim[OF ex1];
			- for x;
				by ex_intro1[of x].
			.
	end

	theory The:
		import The.
	begin
		interpret .Ex1.
		lemma THE_eq_intro: if ex1: ∃!y. P.[y], Px: P.[x] then (THE y. P.[y]) = x;
			apply ex1_elim[OF ex1];
			- for z if Pz: P.[z], 1: ∀y. P.[y] ⟹ y = z;
				have zT: (THE x. P.[x]) = z;
					by 1[OF ex1_imp_THE[OF ex1]].
				unfold zT;
				unfold 1[OF Px].
			.
		note eq_THE_intro: THE_eq_intro[THEN eq.sym].
	end

	theory ExRel:
		import ExRel.
	begin
		lemma ex_cong:
			if ab: a = b, PQ: ∀x. x < b ⟹ P.[x] ⟺ Q.[x]
			then (∃x < a. P.[x]) ⟺ (∃x < b. Q.[x]);
		-	apply iff_intro;
			- if Pa;
				apply ex_elim[OF Pa];
				- for x;
					by ex_intro1[of x] #unfold ab #fold PQ.
				.
			- if Qb;
				apply ex_elim[OF Qb];
				- for x;
					by ex_intro1[of x] #unfold ab PQ.
				.
			.
		.
		lemma ex_eq_iff: (∃x < a. x = b) ⟺ b < a;
			apply iff_intro;
			- if ex;
				apply ex_elim[OF ex];
				- if xa: x < a, xb: x = b;
					by xa[unfold xb].
				.
			- if ba: b < a;
				apply ex_intro1[OF ba].
			.
		lemma ex_eq_and_iff: (∃x < a. x = b ∧ P.[x]) ⟺ (b < a ∧ P.[b]);
			have 1: (∃x < a. x = b ∧ P.[x]) ⟺ (∃x. x = b ∧ x < a ∧ P.[x]);
				unfold ex_def;
				apply TypeFree.ex_cong;
				by iff_intro.
			unfold 1;
			unfold and.left_assoc ex_eq_and_iff.

	end

	theory AllExRel:
		import AllExRel.
	begin
		interpret local.AllRel.
		interpret .ExRel.
	end

	theory Ex1Rel:
		import AllExRel.
		fix (∃!<).
		assume ex1_def: (∃!x < a. P.[x]) = (∃x < a. P.[x] ∧ (∀y < a. P.[y] ⟹ y = x)).
	begin
		note(cong) all_cong ex_cong.
		lemma ex1_cong(cong)
			if eq: a = b, iff: ∀x. x < b ⟹ P.[x] ⟺ P'.[x] then (∃!x < a. P.[x]) ⟺ (∃!x < b. P'.[x]);
			simp ex1_def eq iff;.
		lemma ex1_intro1:
			for x a P if Px: P.[x], x: x < a, uniq: ∀y < a. P.[y] ⟹ y = x then ∃!x < a. P.[x];
			unfold ex1_def;
			by ex_intro1[of x] Px x uniq.
		lemma ex1_elim:
			if ex1: ∃!x < a. P.[x], imp: ∀x. x < a ⟹ P.[x] ⟹ (∀y < a. P.[y] ⟹ y = x) ⟹ Q then Q;
			apply ex1[unfold ex1_def, THEN ex_elim];
			unfold and_imp_iff_imp_imp;
			- for x;
				by imp[of x].
			.
		lemma ex1_eq_and_iff: for P then (∃!x < a. x = b ∧ P.[x]) ⟺ b < a ∧ P.[b];
			simp ex1_def and.left_assoc ex_eq_and_iff;
			by iff_intro.
		lemma ex1_eq_iff: (∃!x < a. x = b) ⟺ b < a;
			by ex1_eq_and_iff[of (x. true), simp].
	end

	theory TheRel:
		import Ex1Rel.
		fix THE.<.
		assume THE_intro: (∃!x < a. P.[x]) ⟹ P.[THE x < a. P.[x]].
		assume THE_in: (∃!x < a. P.[x]) ⟹ (THE x < a. P.[x]) < a.
	begin
		lemma THE_eq_intro: if ex1: ∃!y < a. P.[y], Px: P.[x], xa: x < a then (THE y < a. P.[y]) = x;
			apply ex1_elim[OF ex1];
			- for z if za: z < a, Pz: P.[z], 1: ∀y < a. P.[y] ⟹ y = z;
				note imp: 1[unfold all_def].
				have zT: (THE x < a. P.[x]) = z;
					by imp THE_intro ex1 THE_in.
				unfold zT;
				by Px xa #unfold imp.
			.
		note eq_THE_intro: THE_eq_intro[THEN eq.sym].
	end

	theory Membership:
		import local? local.Membership.
		import in: Ex1Rel (∈) (∀∈) (∃∈) (∃!∈).
		import sub: Ex1Rel (⊆) (∀⊆) (∃⊆) (∃!⊆).
	begin
		interpret Iff.
		note(cong) in.all_cong in.ex_cong in.ex1_cong sub.all_cong sub.ex_cong sub.ex1_cong.
		note(simp) in.ex_imp_iff sub.ex_imp_iff.
	end

	theory Prod: --- Product Class ---
		import Membership.
		import .Pair.
		fix (×).
		assume in_prod_iff: p ∈ A × B ⟺ (∃x ∈ A. ∃y ∈ B. p = (x,y)).
	begin
		lemma pair_in_prod_iff(simp) (x,y) ∈ A × B ⟺ x ∈ A ∧ y ∈ B;
			apply iff_intro;
			simp in_prod_iff;
			- if x': x' ∈ A, y': y' ∈ B, xx': x = x', yy': y = y';
				by x' y' #unfold xx' yy'.
			- if x: x ∈ A, y: y ∈ B;
				by in.ex_intro1[OF x] in.ex_intro1[OF y].
			.
		lemma pair_in_prod: if x: x ∈ A, y: y ∈ B then (x,y) ∈ A × B;
			unfold in_prod_iff;
			apply in.ex_intro1[OF x] in.ex_intro1[OF y].

	end

end

theory Intuitionistic:
	import Intuitionistic.
begin
	interpret .Minimal.
end

theory Classical:
	import Classical.
begin
	interpret .Intuitionistic.
end

theory Typed:
	import Typed.
	fix Eq.
	import eq: Binary (=) Eq Eq Prop.
begin

	note! eq.closed.

end

