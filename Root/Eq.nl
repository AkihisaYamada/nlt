---
# Equality
---

import Base.

fix (=).

namespace eq:
	import MetaReflexive (=).
	assume elim: for X y z if y = z, X.[y] then X.[z].
end

begin
---
## Theorems
---

note! eq.refl.

interpret MetaMagmas (=).

---
Equality is an equivalence.
---
context eq begin
	interpret MetaEquivalence (=);
		- if xy: x = y then y = x;
			by elim[of (z. z = x), OF xy].
		- if xy: x = y, yz: y = z then x = z;
			by elim[of (w. x = w), OF yz xy].
		.
	lemma cong_meta: for X if yz: y = z then X.[y] = X.[z];
		by elim[of (w. X.[y] = X.[w]), OF yz refl].
	lemma imp: if PQ: P = Q, P: P then Q;
		by elim[of (x. x), OF PQ P].

	lemma imp_rev: if PQ: P = Q, Q: Q then P;
		by imp[OF sym[OF PQ] Q].
end

set rewrite eq.imp eq.imp_rev eq.refl eq.trans.
set dual eq.sym.

lemma arg_cong: if xy: x = y then f x = f y;
	by eq.cong_meta[of (z. f z), OF xy].

lemma fun_cong: if fg: f = g then f x = g x;
	by eq.cong_meta[of (h. h x), OF fg].

context eq begin
	lemma cong: if fg: f = g, xy: x = y then f x = g y;
		have 1: f x = f y;
			by arg_cong[OF xy].
		apply trans[OF 1];
		by fun_cong[OF fg].
end

note(fallback) eq.cong.

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
			by 1[unfolded inverse].
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

theory Ex1:
	fix (∃!).
	assume ex1_intro1: for x P if P.[x], ∀y. P.[y] ⟹ y = x then ∃!x. P.[x].
	assume ex1_elim: if ∃!x. P.[x], ∀x. P.[x] ⟹ (∀y. P.[y] ⟹ y = x) ⟹ Q then Q.
begin
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
begin
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

theory Iff:
	import Iff.
begin
	lemma eq_imp_iff(fallback) if eq: P = Q then P ⟺ Q;
		unfold[on (=)] eq;
		.
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

theory Minimal:
	import Iff.
	import Minimal.
	import Ex1.
begin
	lemma eq_refl_iff(simp) x = x ⟺ true;
		by iff_intro.
	lemma ex1_imp_ex: if ex1: ∃!x. P.[x] then ∃x. P.[x];
		apply ex1_elim[OF ex1];
		- for x;
			by ex_intro1[of x].
		.
	lemma ex1_iff: (∃!x. P.[x]) ⟺ (∃x. P.[x] ∧ (∀y. P.[y] ⟹ y = x));
		apply iff_intro;
		- if ex1;
			apply ex_intro;
			unfold and_imp_iff_imp_imp;
			apply ex1_elim[OF ex1]=.
		- if ex;
			apply ex1_intro;
			apply ex[unfolded ex_iff and_imp_iff_imp_imp]=.
		.
	lemma ex1_cong_iff(cong)
		if iff: ∀x. P.[x] ⟺ P'.[x] then (∃!x. P.[x]) ⟺ (∃!x. P'.[x]);
		unfold ex1_iff iff.

	theory AllRel:
		import AllRel.
	begin
		lemma cong:
			if AB: A = B, PQ: ∀x. x ∈ B ⟹ P.[x] ⟺ Q.[x]
			then (∀x ∈ A. P.[x]) ⟺ (∀x ∈ B. Q.[x]);
			apply iff_intro;
			- if PA;
				apply intro;
				by elim1[OF PA, unfolded AB] #fold PQ.
			- if QB;
				apply intro;
				by elim1[OF QB] #unfold AB PQ.
			.
	end
	theory ExRel:
		import ExRel.
	begin
		lemma cong:
			if AB: A = B, PQ: ∀x. x ∈ B ⟹ P.[x] ⟺ Q.[x]
			then (∃x ∈ A. P.[x]) ⟺ (∃x ∈ B. Q.[x]);
			apply iff_intro;
			- if PA;
				apply elim[OF PA];
				- for x;
					by intro1[of x] #unfold AB #fold PQ.
				.
			- if QB;
				apply elim[OF QB];
				- for x;
					by intro1[of x] #unfold AB PQ.
				.
			.
	end
	theory AllEx1Rel:
		import AllExRel.
		fix (∃!<).
		assume ex1_iff: (∃!x < a. P.[x]) ⟺ (∃x < a. P.[x] ∧ (∀y < a. P.[y] ⟹ y = x)).
	begin
		interpret all: .AllRel.
		interpret ex: .ExRel.
		lemma ex1_cong:
			if iff: ∀x. x ∈ A ⟹ P.[x] ⟺ P'.[x] then (∃!x ∈ A. P.[x]) ⟺ (∃!x ∈ A. P'.[x]);
			unfold ex1_iff iff.
		lemma ex1_intro1:
			for x A P if Px: P.[x], x: x ∈ A, uniq: ∀y ∈ A. P.[y] ⟹ y = x then ∃!x ∈ A. P.[x];
			unfold ex1_iff;
			by ex.intro1[of x] Px x uniq.

		lemma ex1_elim: if ex1: ∃!x ∈ A. P.[x], imp: ∀x. x ∈ A ⟹ P.[x] ⟹ (∀y ∈ A. P.[y] ⟹ y = x) ⟹ Q then Q;
			apply ex1[unfolded ex1_iff, THEN ex.elim];
			unfold and_imp_iff_imp_imp;
			- for x;
				by imp[of x].
			.
	end
	theory MetaReflexive:
		import Minimal.MetaReflexive.
	end
	theory MetaPreorder:
		import Minimal.MetaPreorder.
	begin
		interpret .MetaReflexive.
	end
	theory Membership:
		import Membership.
	begin
		interpret in: AllEx1Rel (∈) (∀∈) (∃∈) (∃!∈).
		interpret sub: AllEx1Rel (⊆) (∀⊆) (∃⊆) (∃!⊆).
		theory TheIn:
			fix THE.∈.
			import Ex1In.
			assume TheIn_intro: (∃!x ∈ A. P.[x]) ⟹ P.[THE x ∈ A. P.[x]].
			assume TheIn_in: (∃!x ∈ A. P.[x]) ⟹ (THE x ∈ A. P.[x]) ∈ A.
		begin
			lemma TheIn_eq_intro: if ex1: ∃!y ∈ A. P.[y], Px: P.[x], xA: x ∈ A then (THE y ∈ A. P.[y]) = x;
				apply in.ex1_elim[OF ex1];
				- for z if zA: z ∈ A, Pz: P.[z], 1: ∀y ∈ A. P.[y] ⟹ y = z;
					note imp: 1[unfolded in.all.iff].
					have zT: (THE x ∈ A. P.[x]) = z;
						by imp TheIn_intro ex1 TheIn_in.
					unfold zT;
					by Px xA #unfold imp.
				.
			note TheIn_intro: TheIn_eq_intro[THEN eq.sym].
		end
	end

	theory UnrestrictedComprehension:
		import UnrestrictedComprehension.
	begin
		interpret .Membership.
		---
		Let us call terms of form `{x. P.[x]}` *collections*.
		---
		obtain COLLECT where COLLECT_def: COLLECT = {C. ∃P. C = {x. P.[x]}};
			- for thesis if assm;
				apply assm[OF eq.refl].
			.

		lemma in_COLLECT_iff_ex: X ∈ COLLECT ⟺ (∃P. X = {x. P.[x]});
			unfold COLLECT_def in_Collect_iff;.

		lemma Collect_in_COLLECT: {x. P.[x]} ∈ COLLECT;
			unfold in_COLLECT_iff_ex;
			apply ex_intro;
			- for thesis if assm;
				apply assm[OF eq.refl].
			.

		lemma COLLECT_elim: if A: A ∈ COLLECT, assm: ∀P. A = {x. P.[x]} ⟹ Q then Q;
			apply A[unfolded in_COLLECT_iff_ex, THEN ex_elim, OF assm].

		syntax {} := empty.
		obtain empty where empty_def: {} = {x. false};
			- for thesis if assm;
				apply assm[OF eq.refl].
			.
		lemma in_empty_iff(simp) x ∈ {} ⟺ false;
			simp empty_def in_Collect_iff.

		obtain UNIV where UNIV_def: UNIV = {x. true};
			- for thesis if assm;
				apply assm[OF eq.refl].
			.
		lemma in_UNIV: x ∈ UNIV;
			unfold UNIV_def in_Collect_iff.
		lemma in_UNIV_iff(simp) x ∈ UNIV ⟺ true;
			by iff_intro in_UNIV.

		---
		We will take `(=)` as the equivalence in `COLLECT`.
		---
		namespace COLLECT:
			interpret Equivalence COLLECT (=);
				-; .
				- if xy: x = y; unfold xy.
				- if xy: x = y; unfold xy.
				.
			interpret empty: Member {} COLLECT;
				by empty_def(simp) Collect_in_COLLECT.
			interpret UNIV: Member UNIV COLLECT;
				by UNIV_def(simp) Collect_in_COLLECT.
		end

		---
		The collections form a collection -- leading to Girard's paradox.
		---
		lemma COLLECT_COLLECT: COLLECT ∈ COLLECT;
			unfold[at 0 0 0] COLLECT_def;
			by Collect_in_COLLECT.

	end

	theory Collection:
		import Collect.
		assume Collect_ext(cong) if ∀x. P.[x] ⟺ Q.[x] then {x. P.[x]} = {x. Q.[x]}.
	begin

		lemma Collect_eq_iff: {x. P.[x]} = {x. Q.[x]} ⟺ (∀x. P.[x] ⟺ Q.[x]);
			apply iff_intro;
			- if eq;
				fold in_Collect_iff;
				unfold eq.
			apply Collect_ext>0.

		lemma Collect_in_eq: if A: A ∈ COLLECT then {x. x ∈ A} = A;
			apply COLLECT_elim[OF A];
			- for P if (simp);
				simp in_Collect_iff.
			.

		lemma COLLECT_eq_iff: if A: A ∈ COLLECT, B: B ∈ COLLECT then A = B ⟺ (∀x. x ∈ A ⟺ x ∈ B);
			apply COLLECT_elim[OF A];
			- for P if (simp);
				apply COLLECT_elim[OF B];
				- for Q if (simp);
					simp Collect_eq_iff in_Collect_iff.
				.
			.

	end

	theory Propositional:
		fix Prop EQTYPE.
		import Propositional.
		import .Membership.
		assume eq_type: if A ∈ EQTYPE then (=) ∈ A → A → Prop.
	begin
		lemma eq_prop: if A: A ∈ EQTYPE, x: x ∈ A, y: y ∈ A then (x = y) ∈ Prop;
			by eq_type[OF A, THEN fun_elim1, THEN fun_elim1] x y.
	end

	theory FirstOrder:
		import Propositional.
		import FirstOrder.
		import Ex1In.
		assume ex1In_type: if A ∈ EQTYPE, ∀x ∈ A. P.[x] ∈ Prop then (∃!x ∈ A. P.[x]) ∈ Prop.
	begin
		interpret AllIn.
		interpret ExIn.
	end

	theory HigherOrder:
		import FirstOrder.
		import HigherOrder.
	begin
	end

end

theory Intuitionistic:
	import Minimal.
	import Intuitionistic.
begin
	namespace iff:
		interpret eq: iff.MetaCommutative (=);
			by iff_intro[OF eq.sym eq.sym].
	end
end

theory Ext:
	assume ext: if ∀x ∈ A. f x = g x, A ∈ EQTYPE, B ∈ EQTYPE, f ∈ A → B, g ∈ A → B
	then f = g.
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
			by 1[unfolded fst].
		.
	lemma pair_eq_pair_imp1: if eq: (x,y) = (x',y') then x = x';
		have 1: x = fst (x,y).
		apply eq.trans[OF 1];
		have 2: fst (x,y) = fst (x',y');
			unfold eq.
		apply eq.trans[OF 2];
		have 3: fst (x',y') = x';
			unfold fst.
		by eq.trans[OF 3].

	lemma pair_eq_pair_imp2: if eq: (x,y) = (x',y') then y = y';
		have 1: y = snd (x,y);
			unfold snd.
		apply eq.trans[OF 1];
		have 2: snd (x,y) = snd (x',y');
			unfold eq.
		apply eq.trans[OF 2];
		have 3: snd (x',y') = y';
			unfold snd.
		by eq.trans[OF 3].

	theory UniqueChoice:
		import Ex1.
		assume unique_choice: if ∀x. ∃!y. P.[(x,y)] then ∃f. ∀x. P.[(x, f x)].
	end

end
