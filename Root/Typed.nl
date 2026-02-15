print.
import Membership.

fix Prop.

import imp: Magma Prop (⟹).

fix false.
import false: Member false Prop.

note! imp.closed false.closed.

obtain true where true_intro! true, ! true ∈ Prop;
	- for thesis if assm;
		apply assm[of (false ⟹ false)].
	.

import TypeSafe.
import Membership.
thm in.all_and_distrib.

interpret Member true Prop.
import iff: Magma Prop (⟺).
import and: Magma Prop (∧).
import not: Unary (¬) Prop Prop.

fix QTYPE.

assume all_type! if A ∈ QTYPE, ∀x. x ∈ A ⟹ P.[x] ∈ Prop then (∀x ∈ A. P.[x]) ∈ Prop.

fix (∨).
assume or_intro1: for P Q if P then P ∨ Q.
assume or_intro2: for P Q if Q then P ∨ Q.
assume or_elim: if P ∨ Q, R ∈ Prop, P ⟹ R, Q ⟹ R then R.
import or: Magma Prop (∨).

fix (∃∈).
assume ex_intro1: if x ∈ A, P.[x] then ∃x ∈ A. P.[x].
assume ex_elim: if ∃x ∈ A. P.[x], ∀x. x ∈ A ⟹ P.[x] ⟹ Q, Q ∈ Prop then Q.
assume ex_type! if A ∈ QTYPE, ∀x. x ∈ A ⟹ P.[x] ∈ Prop then (∃x ∈ A. P.[x]) ∈ Prop.

begin
thy.
note! iff.closed and.closed not.closed or.closed.

note(cong) in.all_cong_weak.

interpret iff: Magmas (⟺).
interpret iff_Prop: Equivalence Prop (⟺);
	-.
	- if xy: x ⟺ y; by iff.sym[OF xy].
	- if xy: x ⟺ y, yz: y ⟺ z; by iff.trans[OF xy yz].
	.

---
## Disjunction
---

lemma or_iff_true1(simp) if P: P then P ∨ Q ⟺ true;
	by iff_true or_intro1 P.

lemma or_iff_true2(simp) if Q: Q then P ∨ Q ⟺ true;
	by iff_true or_intro2 Q.

interpret or: Symmetric Prop (∨);
	by #elim or_elim.

---
Algebraic properties of `(∨)`, with respect to `(⟺)`.
Minimal logic does not allow `false` to be neutral of or: `false ∨ P ⟺ P`,
because the `false` case does not derive `P`.
---
interpret or: iff_Prop.MonoMagma (∨);
	- if PQ: P ⟺ Q;
		by iff_intro #elim or_elim #unfold PQ.
	- if PQ: P ⟺ Q;
		by iff_intro #elim or_elim #unfold PQ.
	.
note(cong) or.cong.


interpret or: iff_Prop.CommSemigroupAbsorb (∨) true;
	by iff_intro #elim or_elim.

interpret or: iff.Idempotent Prop (∨);
	by iff_intro #elim or_elim.

lemma or_imp_iff: if !R ∈ Prop then (P ∨ Q ⟹ R) ⟺ (P ⟹ R) ∧ (Q ⟹ R);
	apply iff_intro;
	- if imp;
		by imp.
	by #elim or_elim.

lemma imp_or_if: if or: (P ⟹ Q) ∨ (P ⟹ R), !P, !Q ∈ Prop, !R ∈ Prop then Q ∨ R;
	apply or_elim[OF or].

interpret and_or: iff_Prop.CommSemiring (∧) (∨);
	-.
	- by and.commute.
	-.
	- by or.left_mono.
	- by or.right_mono.
	- if !P ∈ Prop, !Q ∈ Prop, !R ∈ Prop then P ∧ (Q ∨ R) ⟺ P ∧ Q ∨ P ∧ R;
		apply iff_intro;
		simp or_imp_iff imp_and_iff1.
	- by and.left_assoc.
	- by or.commute.
	- by or.left_assoc.
	.

lemma nor_iff: if !P ∈ Prop, !Q ∈ Prop then ¬(P ∨ Q) ⟺ ¬P ∧ ¬Q;
	unfold not_iff_imp_false;
	by or_imp_iff.

lemma nnot_excluded_middle: if !P ∈ Prop then ¬¬(P ∨ ¬P);
	unfold nor_iff;
	by non_contradiction.

lemma nnot_nor_iff: if !P ∈ Prop, !Q ∈ Prop then ¬(¬¬P ∨ Q) ⟺ ¬(P ∨ Q);
	unfold nor_iff nnnot_iff.

lemma nor_nnot_iff: if !P ∈ Prop, !Q ∈ Prop then ¬(P ∨ ¬¬Q) ⟺ ¬(P ∨ Q);
	unfold nor_iff nnnot_iff.

lemma or_imp_nand: if !P ∈ Prop, !Q ∈ Prop then P ∨ Q ⟹ ¬(¬P ∧ ¬Q);
	by not_intro #elim or_elim.

---
## Existence
---
lemma ex_intro:
	if assm: ∀Q. Q ∈ Prop ⟹ (∀x. x ∈ A ⟹ P.[x] ⟹ Q) ⟹ Q, ! A ∈ QTYPE, ! ∀x. x ∈ A ⟹ P.[x] ∈ Prop
	then ∃x ∈ A. P.[x];
	apply assm;
	- for x;
		by ex_intro1[of x].
	.

lemma ex_imp_all_imp:
	if ex: ∃x ∈ A. P.[x] ⟹ Q, all: ∀x ∈ A. P.[x], !Q ∈ Prop then Q;
	apply ex_elim[OF ex];
	- for x if !x ∈ A, imp: P.[x] ⟹ Q;
		by imp all[THEN in.all_elim1].
	.

lemma ex_iff_true:
	if x! x ∈ A, Px: P.[x] then (∃y ∈ A. P.[y]) ⟺ true;
	apply iff_true;
	apply ex_intro1[OF x Px].

lemma ex_iff:
	if !A ∈ QTYPE, ! ∀x. x ∈ A ⟹ P.[x] ∈ Prop
	then (∃x ∈ A. P.[x]) ⟺ (∀Q. Q ∈ Prop ⟹ (∀x. x ∈ A ⟹ P.[x] ⟹ Q) ⟹ Q);
	apply iff_intro;
	- if ex for Q if !, imp;
		apply ex_elim[OF ex];
		apply imp>0=.
	- if all;
		apply ex_intro;
		apply all>0=.
	.

lemma ex_cong:
	if eq: ∀x. x ∈ A ⟹ P.[x] ⟺ P'.[x],
		! A ∈ QTYPE, ! ∀x. x ∈ A ⟹ P.[x] ∈ Prop, ! ∀x. x ∈ A ⟹ P'.[x] ∈ Prop
	then (∃x ∈ A. P.[x]) ⟺ (∃x ∈ A. P'.[x]);
	unfold ex_iff eq.

lemma ex_imp_iff_all(simp)
	if ! A ∈ QTYPE, ! ∀x. x ∈ A ⟹ P.[x] ∈ Prop, ! Q ∈ Prop then ((∃x ∈ A. P.[x]) ⟹ Q) ⟺ (∀x ∈ A. P.[x] ⟹ Q);
	apply+ iff_intro;
	- if imp;
		apply in.all_intro;
		- for x if Px;
			by imp ex_intro1[OF Px].
		.
	- if imp, ex;
		apply ex_elim[OF ex];
		- for x;
			by imp[THEN in.all_elim1, of x].
		.
	.

lemma nex_iff_all_not:
	if ! A ∈ QTYPE, ! ∀x. x ∈ A ⟹ P.[x] ∈ Prop then ¬(∃x ∈ A. P.[x]) ⟺ (∀x ∈ A. ¬P.[x]);
	simp not_iff_imp_false.

lemma ex_or_distrib:
	if ! A ∈ QTYPE, ! ∀x. x ∈ A ⟹ P.[x] ∈ Prop, ! ∀x. x ∈ A ⟹ Q.[x] ∈ Prop
	then (∃x ∈ A. P.[x] ∨ Q.[x]) ⟺ (∃x ∈ A. P.[x]) ∨ (∃x ∈ A. Q.[x]);
	simp iff_iff_and or_imp_iff in.all_and_distrib[dual];
	apply in.all_intro;
	- for x;
		by ex_intro1[of x].
	.