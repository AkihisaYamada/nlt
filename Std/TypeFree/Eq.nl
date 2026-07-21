---
# Type-Free Equality
---
fix (=).

import eq: MetaReflexive (=).

assume eq_elim: for P x y if x = y, P.[x] then P.[y].

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

note#dual eq.sym.

lemma eq_imp: if PQ: P = Q, P: P then Q;
	by eq_elim[of (x. x), OF PQ P].

lemma eq_imp_rev: if PQ: P = Q, Q: Q then P;
	by eq_imp[OF eq.sym[OF PQ] Q].

set simp eq_imp eq_imp_rev eq.refl eq.trans.

lemma eq_cong_meta#cong for X if yz: y = z then X.[y] = X.[z];
	by eq_elim[of (w. X.[y] = X.[w]), OF yz eq.refl].

lemma unbind_cong: if XY: X = Y then X.[z] = Y.[z];
	by eq_cong_meta[of (X. X.[z]), OF XY].

lemma arg_cong: if xy: x = y then f x = f y;
	by eq_cong_meta[of (z. f z), OF xy].

lemma fun_cong: if fg: f = g then f x = g x;
	by eq_cong_meta[of (h. h x), OF fg].

lemma cong#cong? if fg: f = g, xy: x = y then f x = g y;
	have 1: f x = f y;
		by arg_cong[OF xy].
	apply eq.trans[OF 1];
	by fun_cong[OF fg].

---
## Theories
---

theory TwoValued :=
	assume imp_imp_eq: if P, Q then P = Q.
	assume imp_eq: if P then (P ⟹ Q) = Q.
begin
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

theory MetaInjective f :=
	assume inj: if f x = f x' then x = x'.
end

theory MetaInverse f g :=
	assume inverse: g (f x) = x.
begin
	interpret MetaInjective;
		- for x x' if eq: f x = f x';
			have 1: g (f x) = g (f x');
				unfold eq.
			by 1[unfold inverse].
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

theory FunComp :=-- aka B
	fix (∘).
	assume comp_app#simp (f ∘ g) x = f (g x).
end

theory RevApp :=
	fix (|>).
	assume revapp#simp x |> f = f x.
end

theory MetaIf :=
	fix If.
	assume If_then: if P then If P x y = x.
	---
	A minimal specification: P and ¬P will not lead to explosion.
	---
	assume If_else: if P ⟹ x = y then If P x y = y.
begin
end

--- Syntactic Pairing ---
theory MetaPair :=
	fix (,) fst snd.
	assume fst#simp fst (x,y) = x.
	assume snd#simp snd (x,y) = y.
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

	lemma eq_pair_fst#simp[after 1] if p: p = (x,y) then fst p = x;
		simp p.
	lemma eq_pair_snd#simp[after 1] if p: p = (x,y) then snd p = y;
		simp p.
end

theory And :=
	fix (∧).
	assume and_def: (P ∧ Q) = (∀R. (P ⟹ Q ⟹ R) ⟹ R).
begin

	interpret? TypeFree.And;
		by #simp and_def.

end

theory Or :=
	fix (∨).
	assume or_def: (P ∨ Q) = (∀R. (P ⟹ R) ⟹ (Q ⟹ R) ⟹ R).
begin

	interpret TypeFree.Or;
		note#simp or_def.
		- if or: P ∨ Q;
			apply or[unfold or_def]=.
		.

end

theory Ex :=
	fix (∃).
	assume ex_def: (∃x. P.[x]) = (∀Q. (∀x. P.[x] ⟹ Q) ⟹ Q).
begin

	interpret TypeFree.Ex;
		- for x if Px: P.[x] then ∃x. P.[x];
			unfold ex_def;
			- for Q if assm;
				by assm[of x] Px.
			.
		- for P;
			unfold ex_def;
			apply imp.refl>0.
		.

	lemma ex_eq1: ∃x. x = a;
		apply ex_intro1[of a].

	lemma ex_eq2: ∃x. a = x;
		apply ex_intro1[of a].

end

theory Ex1 :=
	fix (∃!).
	assume ex1_def: (∃!x. P.[x]) = (∀Q. (∀x. P.[x] ⟹ (∀y. P.[y] ⟹ y = x) ⟹ Q) ⟹ Q).
begin

	lemma ex1_intro: if assm: ∀Q. (∀x. P.[x] ⟹ (∀y. P.[y] ⟹ y = x) ⟹ Q) ⟹ Q then ∃!x. P.[x];
		apply eq_imp_rev[OF ex1_def];
		apply assm=.

	lemma ex1_intro1: for x P if Px: P.[x], u: ∀y. P.[y] ⟹ y = x then ∃!x. P.[x];
		unfold ex1_def;
		- for Q if assm;
			by assm[of x] Px u.
		.

	lemma ex1_elim: if ex1: ∃!x. P.[x], all: ∀x. P.[x] ⟹ (∀y. P.[y] ⟹ y = x) ⟹ Q then Q;
		apply eq_imp[OF ex1_def ex1, OF all].

	lemma ex1_eq1: ∃!x. x = a;
		apply ex1_intro1[of a].

	lemma ex1_eq2: ∃!x. a = x;
		apply ex1_intro1[of a];
		by #elim eq.sym.

	lemma ex1_imp_unique: if ex1: ∃!x. P.[x], Px: P.[x], Py: P.[y] then y = x;
		apply ex1_elim[OF ex1];
		- for z if Pz, eq;
			unfold eq[OF Px] eq[OF Py].
		.

	extend Ex begin

		lemma ex1_imp_ex: if ex1: ∃!x. P.[x] then ∃x. P.[x];
			apply ex1_elim[OF ex1];
			- for x; by ex_intro1[of x].
			.

	end

end


theory Iff :=
	fix (⟺).
	assume iff_def: (P ⟺ Q) = (∀R. ((P ⟹ Q) ⟹ (Q ⟹ P) ⟹ R) ⟹ R).
begin

	interpret base? TypeFree.Iff;
		- if PQ: P ⟹ Q, QP: Q ⟹ P then P ⟺ Q;
			unfold iff_def;
			- for R if assm then R;
				by assm PQ QP.
			.
		- if PQ: P ⟺ Q;
			apply PQ[unfold iff_def].
		- if PQ: P ⟺ Q;
			apply PQ[unfold iff_def].
		.

	interpret iff_eq: iff.MetaCommutative (=);
		by iff_intro[OF eq.sym eq.sym].

	lemma eq_imp_iff#cong? if eq: P = Q then P ⟺ Q;
		unfold[on (=)] eq.

	lemma all_eq_imp_iff: (∀x. x = a ⟹ P.[x]) ⟺ P.[a];
		apply iff_intro;
		- if all;
			apply all.
		- if Pa: P.[a], xa: x = a;
			by Pa #simp xa.
		.

	lemma eq_refl_iff#simp x = x ⟺ true;
		by iff_intro.

	extend Eq.And begin

		interpret base? base.And;
			by eq_imp_iff[OF and_def].

	end

	extend Eq.Or begin

		interpret base? base.Or;
			by eq_imp_iff[OF or_def].

	end

	extend Eq.Ex begin

		interpret base? base.Ex;
			by eq_imp_iff[OF ex_def].

		extend And begin

			interpret base.And.

			lemma ex_eq_and_iff: (∃x. x = a ∧ P.[x]) ⟺ P.[a];
				apply iff_intro;
				-> if xa: x = a, Px: P.[x];
					by Px #fold xa.
				- if Pa: P.[a];
					by ex_intro1[of a] Pa.
				.
			lemma ex_eq_and_iff2: (∃x. a = x ∧ P.[x]) ⟺ P.[a];
				unfold iff_eq.commute;
				by ex_eq_and_iff.

		end

	end

	extend Ex1 begin

		lemma ex1_cong#cong
			if iff: ∀x. P.[x] ⟺ P'.[x] then (∃!x. P.[x]) ⟺ (∃!x. P'.[x]);
			unfold ex1_def iff.

		note#simp iff_true[OF ex1_eq1] iff_true[OF ex1_eq2].

	end

end
