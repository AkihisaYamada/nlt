-------
# Minimal Logic

This theory assumes the type-free specifications of logical operators.
-------
import Iff.
import And.
fix true false (∨) (¬) (∃).

assume true_intro! true.

assume or_intro1: for P Q if P then P ∨ Q.
assume or_intro2: for P Q if Q then P ∨ Q.
assume or_elim: if P ∨ Q, P ⟹ R, Q ⟹ R then R.

assume not_intro: if P ⟹ false then ¬P.
assume not_imp_false: if ¬P, P then false.

assume ex_intro1: for x if P.[x] then ∃x. P.[x].
assume ex_elim: if ∃x. P.[x], ∀x. P.[x] ⟹ Q then Q.

begin
---
## Theorems
---

interpret imp: iff.MetaLeftNeutral (⟹) true;
	by imp_imp_iff.

interpret imp: iff.MetaRightAbsorb (⟹) true;
	by iff_intro.

interpret iff: iff.MetaCommNeutral (⟺) true;
	by iff_intro #elim iff_elim.

interpret and: iff.MetaCommNeutral (∧) true;
	by iff_intro.

note(simp) imp.left_neutral imp.right_absorb iff.left_neutral iff.right_neutral and.left_neutral and.right_neutral.

lemma iff_true: P ⟹ P ⟺ true.

---
### Negation
---

lemma not_cong(cong) if PQ: P ⟺ Q then ¬P ⟺ ¬Q;
	apply iff_intro;
	- if nP: ¬P;
		by not_intro not_imp_false[OF nP] iff_elim2[OF PQ].
	- if nQ: ¬Q;
		by not_intro not_imp_false[OF nQ] iff_elim1[OF PQ].
	.

lemma not_false: ¬false;
	by not_intro[OF imp.refl].

lemma not_false_iff(simp) ¬false ⟺ true;
	by not_false.

lemma not_iff_imp_false: ¬P ⟺ (P ⟹ false);
	by iff_intro[OF not_imp_false not_intro].

lemma not_true_iff(simp) ¬true ⟺ false;
	unfold not_iff_imp_false.

lemma imp_not: if [P], nQ: ¬Q then ¬(P ⟹ Q);
	apply not_intro;
	- if PQ: P ⟹ Q;
		by not_imp_false[OF nQ] PQ.
	.

lemma imp_not_imp: if PQ: P ⟹ Q, nQ: ¬Q then ¬P;
	by not_intro not_imp_false[OF nQ] PQ.

lemma imp_not_sym: if PnQ: P ⟹ ¬Q, Q: Q then ¬P;
	apply not_intro;
	- if P: P;
		by not_imp_false[OF PnQ[OF P] Q].
	.

lemma nnot_intro: if P: P then ¬¬P;
	apply not_intro;
	- if nP: ¬P;
		by not_imp_false[OF nP P].
	.

lemma not_imp_not_all: if nPx: ¬P.[x] then ¬(∀y. P.[y]);
	by not_intro not_imp_false[OF nPx].

lemma imp_not_commute: (P ⟹ ¬Q) ⟺ (Q ⟹ ¬P);
	by iff_intro[OF imp_not_sym imp_not_sym].

lemma nnnot_iff: ¬¬¬P ⟺ ¬P;
	unfold+ not_iff_imp_false;
	by imp3_iff.

lemma nnot_imp_not_iff: (¬¬P ⟹ ¬Q) ⟺ (P ⟹ ¬Q);
	unfold imp_not_commute;
	unfold nnnot_iff.

lemma nnimp_imp_nnot: if nnPQ: ¬¬(P ⟹ Q), [P] then ¬¬Q;
	apply not_intro;
	- if nQ: ¬Q;
		apply+ not_imp_false[OF nnPQ] not_intro;
		- if PQ: P ⟹ Q;
			by not_imp_false[OF nQ] PQ.
		.
	.

lemma nnimp_not_iff: ¬¬(P ⟹ ¬Q) ⟺ (P ⟹ ¬Q);
	apply iff_intro;
	- if nnimp: ¬¬(P ⟹ ¬Q), P: P then ¬Q;
		by nnimp_imp_nnot[OF nnimp P, unfolded nnnot_iff].
	by nnot_intro.

lemma nnot_imp: if imp: ¬¬P ⟹ Q then P ⟹ Q;
	by imp nnot_intro.

lemma nnot_imp_nnot: if nnP: ¬¬P, PQ: P ⟹ Q then ¬¬Q;
	apply not_intro;
	- if !¬Q;
		have! ¬P;
			by imp_not_imp[OF PQ].
		by not_imp_false[OF nnP].
	.

lemma nnot_not_imp_nimp: if nnP: ¬¬P, [¬Q] then ¬(P ⟹ Q);
	apply not_intro;
	- if PQ: P ⟹ Q;
		have nnQ: ¬¬Q;
			by nnot_imp_nnot[OF nnP PQ].
		by not_imp_false[OF nnQ].
	.


---
### Conjunction
---

lemma nand_intro1: if nP: ¬P then ¬(P ∧ Q);
	by not_intro not_imp_false[OF nP].

lemma nand_intro2: if nQ: ¬Q then ¬(P ∧ Q);
	by not_intro not_imp_false[OF nQ].

lemma nand_iff_imp_not: ¬(P ∧ Q) ⟺ (P ⟹ ¬Q);
	simp not_iff_imp_false.

lemma non_contradiction: ¬(P ∧ ¬P);
	unfold nand_iff_imp_not;
	by nnot_intro.

lemma nand_nnot_iff: ¬(P ∧ ¬¬Q) ⟺ ¬(P ∧ Q);
	unfold+ nand_iff_imp_not nnnot_iff.

lemma nnot_nand_iff: ¬(¬¬P ∧ Q) ⟺ ¬(P ∧ Q);
	unfold and.commute;
	unfold nand_nnot_iff;
	unfold and.commute.

---
### Disjunction
---

lemma or_intro: if assm: ∀R. (P ⟹ R) ⟹ (Q ⟹ R) ⟹ R then P ∨ Q;
	by assm[OF or_intro1 or_intro2].

lemma or_iff: P ∨ Q ⟺ (∀R. (P ⟹ R) ⟹ (Q ⟹ R) ⟹ R);
	apply iff_intro[OF or_elim or_intro].

interpret or: MetaSymmetric (∨);
	by or_intro #elim or_elim.

lemma or_iff_true1: if ! P then P ∨ Q ⟺ true;
	by iff_intro or_intro1.

lemma or_iff_true2: if ! Q then P ∨ Q ⟺ true;
	by iff_intro or_intro2.

---
Algebraic properties of `(∨)`, with respect to `(⟺)`.
Minimal logic does not allow `false` to be neutral of or: `false ∨ P ⟺ P`,
because the `false` case does not derive `P`.
---
interpret or: iff.MetaCompatible (∨);
	- if PQ: P ⟺ Q, RS: R ⟺ S then P ∨ R ⟺ Q ∨ S;
		by iff_intro or_intro #elim or_elim #unfold PQ RS.
	.
note(cong) or.cong.

interpret or: iff.MetaCommAbsorb (∨) true;
	- by iff_intro or_intro.
	- by iff_intro[OF or.sym or.sym].
	.

note(simp) or.left_absorb or.right_absorb.

interpret or: iff.MetaAssociative (∨);
	by iff_intro #elim or_elim #unfold or_iff_true1 or_iff_true2.

interpret or: iff.MetaIdempotent (∨);
	- then P ∨ P ⟺ P;
		by iff_intro or_intro or_elim(elim).
	.

lemma or_imp_iff: (P ∨ Q ⟹ R) ⟺ (P ⟹ R) ∧ (Q ⟹ R);
	apply iff_intro;
	- if imp;
		by imp or_intro.
	by #elim or_elim.

lemma imp_or_if: if or: (P ⟹ Q) ∨ (P ⟹ R), !P then Q ∨ R;
	by or[unfolded imp_imp_iff].

lemma and_or_distrib: P ∧ (Q ∨ R) ⟺ P ∧ Q ∨ P ∧ R;
	apply iff_intro;
	simp or_imp_iff;
	by or_intro.

lemma or_and_distrib: (P ∨ Q) ∧ R ⟺ P ∧ R ∨ Q ∧ R;
	unfold and.commute;
	unfold and_or_distrib.

lemma nor_iff: ¬(P ∨ Q) ⟺ ¬P ∧ ¬Q;
	unfold not_iff_imp_false;
	by or_imp_iff.

lemma nnot_excluded_middle: ¬¬(P ∨ ¬P);
	unfold nor_iff;
	by non_contradiction.

lemma nnot_nor_iff: ¬(¬¬P ∨ Q) ⟺ ¬(P ∨ Q);
	unfold nor_iff nnnot_iff.

lemma nor_nnot_iff: ¬(P ∨ ¬¬Q) ⟺ ¬(P ∨ Q);
	unfold nor_iff nnnot_iff.

lemma nnand_iff: ¬¬(P ∧ Q) ⟺ ¬¬P ∧ ¬¬Q;
	fold nnot_nand_iff;
	fold nand_nnot_iff;
	fold nor_iff;
	unfold nnnot_iff;
	unfold nor_iff.

lemma or_imp_nand: if PQ: P ∨ Q then ¬(¬P ∧ ¬Q);
	apply not_intro;
	- if and: ¬P ∧ ¬Q;
		have nP: ¬P;
			by and_elim1[OF and].
		have nQ: ¬Q;
			by and_elim2[OF and].
		apply or_elim[OF PQ];
		- by not_imp_false[OF nP].
		- by not_imp_false[OF nQ].
		.
	.

---
### Existence
---
lemma ex_intro: if assm: ∀Q. (∀x. P.[x] ⟹ Q) ⟹ Q then ∃x. P.[x];
	apply assm;
	- for x;
		by ex_intro1[of x].
	.

lemma ex_imp_all_imp: if ex: ∃x. P.[x] ⟹ Q, [∀x. P.[x]] then Q;
	apply ex_elim[OF ex];
	- for x if imp: P.[x] ⟹ Q;
		by imp.
	.
lemma ex_iff: (∃x. P.[x]) ⟺ (∀Q. (∀x. P.[x] ⟹ Q) ⟹ Q);
	apply iff_intro[OF ex_elim];
	apply ex_intro>0.

lemma ex_cong(cong) if eq: ∀x. P.[x] ⟺ P'.[x] then (∃x. P.[x]) ⟺ (∃x. P'.[x]);
	unfold ex_iff eq.

lemma ex_indep(simp) (∃x. P) ⟺ P;
	apply iff_intro;
	- by ex_elim(elim).
	- if P; by ex_intro1 P.
	.

lemma ex_imp_iff_all(simp) ((∃x. P.[x]) ⟹ Q) ⟺ (∀x. P.[x] ⟹ Q);
	apply iff_intro;
	- if imp: (∃x. P.[x]) ⟹ Q for x if Px: P.[x];
		by imp ex_intro1[OF Px].
	- if imp: ∀x. P.[x] ⟹ Q, ex: ∃x. P.[x];
		obtain x where Px: P.[x];
			- for thesis;
				apply ex[unfolded ex_iff, of thesis]=.
			.
		by imp[OF Px].
	.

lemma ex_or_distrib: (∃x. P.[x] ∨ Q.[x]) ⟺ (∃x. P.[x]) ∨ (∃x. Q.[x]);
	apply iff_intro;
	- if ex;
		apply ex_elim[OF ex];
		- if or: P.[x] ∨ Q.[x];
			apply or_elim[OF or];
			- if Px;
				unfold iff_true[OF ex_intro1[OF Px]].
			- if Qx;
				unfold iff_true[OF ex_intro1[OF Qx]].
			.
		.
	- if or;
		apply or_elim[OF or];
		- if ex;
			apply ex_elim[OF ex];
			- if Px: P.[x];
				apply ex_intro1[of x];
				unfold iff_true[OF Px];.
			.
		- if ex;
			apply ex_elim[OF ex];
			- if Qx: Q.[x];
				apply ex_intro1[of x];
				unfold iff_true[OF Qx];.
			.
		.
	.

lemma nex_iff_all_not: ¬(∃x. P.[x]) ⟺ (∀x. ¬P.[x]);
	simp not_iff_imp_false.

---
### Double negation and universal quantification.

The following direction is provable in general, but the opposite direction requires something similar to the axiom of choice.
---
lemma nnall_imp: if nnall: ¬¬(∀x. P.[x]) then ∀x. ¬¬P.[x];
	- for x;
		apply not_intro;
		- if nPx: ¬P.[x];
			by not_imp_false[OF nnall] not_imp_not_all[OF nPx].
		.
	.

---
The other direction is provable if inside the quantification has negation.
---
lemma nnall_not_iff: ¬¬(∀x. ¬P.[x]) ⟺ (∀x. ¬P.[x]);
	fold nex_iff_all_not;
	by nnnot_iff.

---
## Theories
---

theory AllExRel:
	import AllRel.
	import ExRel.
begin
	lemma ex_iff_ex: (∃x < a. P.[x]) ⟺ (∃x. x < a ∧ P.[x]);
		unfold ex_def ex_iff.
	lemma nex_iff_all_not: ¬(∃x < a. P.[x]) ⟺ (∀x < a. ¬ P.[x]);
		unfold ex_iff_ex all_def .nex_iff_all_not nand_iff_imp_not.
	lemma all_true_iff: (∀x < a. true) ⟺ true;
		simp all_def.
	lemma ex_or_distrib: (∃x < a. P.[x] ∨ Q.[x]) ⟺ (∃x < a. P.[x]) ∨ (∃x < a. Q.[x]);
		simp ex_iff_ex and_or_distrib .ex_or_distrib.
end

---
The logical operators allow us to define some properties.
---
theory MetaIrreflexive:
	fix (<).
	assume irrefl: ¬ x < x.
end

theory MetaAsymmetric:
	fix (<).
	assume asym: x < y ⟹ ¬ y < x.
end
---
Note that antisymmetry is not yet definable, because it requires equality.
---
theory MetaOrder:
	import MetaIrreflexive.
	import MetaTransitive (<).
begin
	interpret MetaAsymmetric;
		- for x y if xy: x < y then ¬ y < x;
			apply not_intro;
			- if yx: y < x;
				have xx: x < x;
					by trans[OF xy yx].
				by not_imp_false[OF irrefl xx].
			.
		.
end

theory Membership:
	import ..Membership.
	import in: AllExRel (∈) (∀∈) (∃∈).
	fix (⊆).
	assume subseteq_iff_allIn: A ⊆ B ⟺ (∀x ∈ A. x ∈ B).
	import sub: AllExRel (⊆) (∀⊆) (∃⊆).
begin

end

theory Propositional:
	fix Prop.
	import Fun.
	import .Membership.
	import true: Member true Prop.
	import false: Member false Prop.
	import imp: Magma Prop (⟹).
	import iff: Magma Prop (⟺).
	import and: Magma Prop (∧).
	import or: Magma Prop (∨).
	import not: Unary (¬) Prop Prop.
begin
	note! true.closed false.closed imp.closed iff.closed and.closed or.closed not.closed.
end

theory FirstOrder:
	fix QTYPE.
	import Propositional.
	assume allIn_prop! if A ∈ QTYPE, ∀x. x ∈ A ⟹ P.[x] ∈ Prop then (∀x ∈ A. P.[x]) ∈ Prop.
	assume exIn_prop! if A ∈ QTYPE, ∀x. x ∈ A ⟹ P.[x] ∈ Prop then (∃x ∈ A. P.[x]) ∈ Prop.
begin
	theory Impredicative:
		assume Prop_type: Prop ∈ QTYPE.
	end
end

theory SecondOrder:
	fix IND.
	import FirstOrder.
	assume IND_type: if A ∈ IND then A ∈ QTYPE.
	assume IND_Fun_type: if A ∈ IND, B ∈ QTYPE then A → B ∈ QTYPE.
begin
	theory Impredicative:
		import Impredicative.
	end
end

theory HigherOrder:
	import FirstOrder.
	assume fun_type: if A ∈ QTYPE, B ∈ QTYPE then A → B ∈ QTYPE.
begin
	theory Impredicative:
		import Impredicative.
	end
end

theory Choice:
	assume choice: (∀x. ∃y. P x y) ⟹ ∃f. ∀x. P x (f x).
end

theory ChoiceOperator:
	fix (SOME).
	assume ex_imp_SOME: (∃x. P.[x]) ⟹ P.[SOME x. P.[y]].
end

theory RestrictedComprehension:
	import Membership.
	fix _CollectIn.
	assume in_CollectIn_iff: x ∈ {x ∈ A. P.[x]} ⟺ x ∈ A ∧ P.[x].
begin

end
