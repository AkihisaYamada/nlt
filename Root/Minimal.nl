-------
# Minimal Logic

This theory assumes the type-free specifications of logical operators.
-------
import TypeSafe.
fix (∨) (∃).

assume or_intro1? for P Q if P then P ∨ Q.
assume or_intro2? for P Q if Q then P ∨ Q.
assume or_elim: if P ∨ Q, P ⟹ R, Q ⟹ R then R.

assume ex_intro1: for x if P.[x] then ∃x. P.[x].
assume ex_elim: if ∃x. P.[x], ∀x. P.[x] ⟹ Q then Q.

begin
---
## Disjunction
---
lemma or_intro: if assm: ∀R. (P ⟹ R) ⟹ (Q ⟹ R) ⟹ R then P ∨ Q;
	apply assm.

lemma or_iff: P ∨ Q ⟺ (∀R. (P ⟹ R) ⟹ (Q ⟹ R) ⟹ R);
	apply iff_intro[OF or_elim or_intro].

interpret or: MetaSymmetric (∨);
	by #elim or_elim.

lemma or_iff_true1: if ! P then P ∨ Q ⟺ true;
	by iff_intro.

lemma or_iff_true2: if ! Q then P ∨ Q ⟺ true;
	by iff_intro.

---
Algebraic properties of `(∨)`, with respect to `(⟺)`.
Minimal logic does not allow `false` to be neutral of or: `false ∨ P ⟺ P`,
because the `false` case does not derive `P`.
---
interpret or: iff.MetaCompatible (∨);
	- if PQ: P ⟺ Q, RS: R ⟺ S then P ∨ R ⟺ Q ∨ S;
		by iff_intro #elim or_elim #unfold PQ RS.
	.
note(cong) or.cong.

interpret or: iff.MetaCommAbsorb (∨) true;
	- by iff_intro.
	- by iff_intro[OF or.sym or.sym].
	.

note(simp) or.left_absorb or.right_absorb.

interpret or: iff.MetaAssociative (∨);
	by iff_intro #elim or_elim #unfold or_iff_true1 or_iff_true2.

interpret or: iff.MetaIdempotent (∨);
	- then P ∨ P ⟺ P;
		by iff_intro or_elim(elim).
	.

lemma or_imp_iff: (P ∨ Q ⟹ R) ⟺ (P ⟹ R) ∧ (Q ⟹ R);
	apply iff_intro;
	- if imp;
		by imp.
	by #elim or_elim.

lemma imp_or_if: if or: (P ⟹ Q) ∨ (P ⟹ R), !P then Q ∨ R;
	by or[unfold imp_imp_iff].

lemma and_or_distrib: P ∧ (Q ∨ R) ⟺ P ∧ Q ∨ P ∧ R;
	apply iff_intro;
	simp or_imp_iff.

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

lemma or_imp_nand: P ∨ Q ⟹ ¬(¬P ∧ ¬Q);
	by not_intro #elim or_elim.

---
## Existence
---
lemma ex_intro: if assm: ∀Q. (∀x. P.[x] ⟹ Q) ⟹ Q then ∃x. P.[x];
	apply assm;
	- for x;
		by ex_intro1[of x].
	.

lemma ex_imp_all_imp: if ex: ∃x. P.[x] ⟹ Q, all: ∀x. P.[x] then Q;
	apply ex_elim[OF ex];
	- for x if imp: P.[x] ⟹ Q;
		by imp all.
	.

lemma ex_iff_true: for x if Px: P.[x] then (∃y. P.[y]) ⟺ true;
	apply iff_true;
	apply ex_intro1[OF Px].

lemma ex_iff: (∃x. P.[x]) ⟺ (∀Q. (∀x. P.[x] ⟹ Q) ⟹ Q);
	apply iff_intro;
	- apply ex_elim>0.
	- apply ex_intro>0.
	.

lemma ex_cong(cong) if eq: ∀x. P.[x] ⟺ P'.[x] then (∃x. P.[x]) ⟺ (∃x. P'.[x]);
	unfold ex_iff eq.

lemma ex_indep(simp) (∃x. P) ⟺ P;
	by iff_intro ex_intro1 ex_elim(elim).

lemma ex_imp_iff_all(simp) ((∃x. P.[x]) ⟹ Q) ⟺ (∀x. P.[x] ⟹ Q);
	apply iff_intro;
	- if imp: (∃x. P.[x]) ⟹ Q for x if Px: P.[x];
		by imp ex_intro1[OF Px].
	- if imp: ∀x. P.[x] ⟹ Q;
		by #elim imp ex_elim.
	.

lemma nex_iff_all_not: ¬(∃x. P.[x]) ⟺ (∀x. ¬P.[x]);
	simp not_iff_imp_false.

lemma ex_or_distrib: (∃x. P.[x] ∨ Q.[x]) ⟺ (∃x. P.[x]) ∨ (∃x. Q.[x]);
	simp iff_iff_and or_imp_iff all_and_distrib[dual];
	- for x;
		by ex_intro1[of x].
	.

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

theory Membership:
	import .Membership.
	import in: AllExRel (∈) (∀∈) (∃∈).
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
