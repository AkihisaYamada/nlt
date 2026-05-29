---
## Propositional Logics

We fix a class `Prop` in which logical operators are closed.
---
import Membership.
import Magmas.

fix Prop (∧) (∨) (¬) (⟺) false.
import imp: Magma Prop (⟹).
import and: Magma Prop (∧).
import or: Magma Prop (∨).
import not: Unary (¬) Prop Prop.
import iff: Magma Prop (⟺).
assume false_type! false ∈ Prop.


begin

interpret? TypeFree.

note! imp.closed and.closed or.closed not.closed iff.closed.

-- `true` is obtained via `false ⟹ false`.
obtain true where true_intro! true, true_type! true ∈ Prop;
	- for thesis if assm;
		apply assm[of (false ⟹ false)].
	.

interpret iff: Magmas.MetaRelation (⟺).

extend TypeSafeMinimal begin

	interpret iff_Prop: Equivalence Prop (⟺);
		-.
		- if xy: x ⟺ y; by iff.sym[OF xy].
		- if xy: x ⟺ y, yz: y ⟺ z; by iff.trans[OF xy yz].
		.
	interpret and_Prop: iff_Prop.CommMonoid (∧) true;
		by and.commute and.left_assoc.

end

extend Minimal begin

	interpret Propositional.TypeSafeMinimal.

	interpret or_Prop: Symmetric Prop (∨);
		by #elim or_elim.
print.
	interpret or_Prop: iff_Prop.CommMonoMagma (∨);
		by or.left_mono.

	interpret or_Prop: iff_Prop.CommSemigroupAbsorb (∨) true;
		by or.commute or.left_assoc.

	interpret or_Prop: iff.Idempotent Prop (∨).

	interpret and_or_Prop: iff_Prop.CommSemiring (∧) (∨);
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

	lemma nnot_excluded_middle: if !P ∈ Prop then ¬ ¬(P ∨ ¬P);
		unfold nor_iff;
		by non_contradiction.

	lemma nnot_nor_iff: if !P ∈ Prop, !Q ∈ Prop then ¬ (¬ ¬ P ∨ Q) ⟺ ¬(P ∨ Q);
		unfold nor_iff nnnot_iff.

	lemma nor_nnot_iff: if !P ∈ Prop, !Q ∈ Prop then ¬(P ∨ ¬ ¬ Q) ⟺ ¬(P ∨ Q);
		unfold nor_iff nnnot_iff.

	lemma or_imp_nand: if !P ∈ Prop, !Q ∈ Prop then P ∨ Q ⟹ ¬(¬P ∧ ¬Q);
		by not_intro #elim or_elim.
	---
	## Existence
	---
	lemma ex_imp_all_imp:
		if ex: ∃x. P.[x] ⟹ Q, all: ∀x. P.[x], !Q ∈ Prop then Q;
		apply ex_elim[OF ex];
		- for x if imp: P.[x] ⟹ Q;
			by imp all.
		.
	lemma ex_imp_iff_all#simp
		if ! Q ∈ Prop then ((∃x. P.[x]) ⟹ Q) ⟺ (∀x. P.[x] ⟹ Q);
		apply iff_intro;
		- if imp, Px: P.[x];
			by imp ex_intro1[OF Px].
		- if imp, ex;
			apply ex_elim[OF ex];
			- for x;
				by imp[of x].
			.
		.
	lemma nex_iff_all_not: ¬(∃x. P.[x]) ⟺ (∀x. ¬ P.[x]);
		simp not_iff_imp_false.

end



theory WeakMinimal:
	--- Typed logic allows elimination rules only derive propositions. ---
	import TypeSafeMinimal.
	assume or_elim: if P ∨ Q, R ∈ Prop, P ⟹ R, Q ⟹ R then R.
	assume ex_elim: if ∃x. P.[x], ∀x. P.[x] ⟹ Q, Q ∈ Prop then Q.
begin

	interpret or: Symmetric Prop (∨);
		by #elim or_elim.

	---
	Algebraic properties of `(∨)`, with respect to `(⟺)`.
	Minimal logic does not allow `false` to be neutral of or: `false ∨ P ⟺ P`,
	because the `false` case does not derive `P`.
	---
	interpret or: iff_Prop.MonoMagma (∨);
		- if PQ: P ⟺ Q;
			by iff_intro #elim or_elim #simp PQ.
		- if PQ: P ⟺ Q;
			by iff_intro #elim or_elim #simp PQ.
		.
	note#cong or.cong.

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

	lemma nnot_excluded_middle: if !P ∈ Prop then ¬ ¬(P ∨ ¬P);
		unfold nor_iff;
		by non_contradiction.

	lemma nnot_nor_iff: if !P ∈ Prop, !Q ∈ Prop then ¬ (¬ ¬ P ∨ Q) ⟺ ¬(P ∨ Q);
		unfold nor_iff nnnot_iff.

	lemma nor_nnot_iff: if !P ∈ Prop, !Q ∈ Prop then ¬(P ∨ ¬ ¬ Q) ⟺ ¬(P ∨ Q);
		unfold nor_iff nnnot_iff.

	lemma or_imp_nand: if !P ∈ Prop, !Q ∈ Prop then P ∨ Q ⟹ ¬(¬P ∧ ¬Q);
		by not_intro #elim or_elim.
	---
	## Existence
	---
	lemma ex_imp_all_imp:
		if ex: ∃x. P.[x] ⟹ Q, all: ∀x. P.[x], !Q ∈ Prop then Q;
		apply ex_elim[OF ex];
		- for x if imp: P.[x] ⟹ Q;
			by imp all.
		.
	lemma ex_imp_iff_all#simp
		if ! Q ∈ Prop then ((∃x. P.[x]) ⟹ Q) ⟺ (∀x. P.[x] ⟹ Q);
		apply iff_intro;
		- if imp, Px: P.[x];
			by imp ex_intro1[OF Px].
		- if imp, ex;
			apply ex_elim[OF ex];
			- for x;
				by imp[of x].
			.
		.
	lemma nex_iff_all_not: ¬(∃x. P.[x]) ⟺ (∀x. ¬ P.[x]);
		simp not_iff_imp_false.

end

theory Intuitionistic:
	--- Typed intuitionistic logic allows false imply any *proposition*. ---
	import Minimal.
	assume false_elim: if false, P ∈ Prop then P.
begin

	lemma not_imp_iff_false: if nP: ¬P, !P ∈ Prop then P ⟺ false;
		by iff_intro not_imp_false[OF nP] #elim false_elim.

	lemma false_imp_iff#simp if ! P ∈ Prop then (false ⟹ P) ⟺ true;
		by iff_true #elim false_elim.

	interpret and: iff_Prop.CommMonoidAbsorb (∧) false true;
		by iff_intro #elim false_elim.

	interpret or: iff_Prop.CommMonoidAbsorb (∨) true false;
		by iff_intro #elim or_elim false_elim.

	note#simp and.left_absorb and.right_absorb or.left_neutral or.right_neutral.

	lemma not_elim: if nP: ¬P, P: P, ! Q ∈ Prop then Q;
		apply false_elim;
		by not_imp_false[OF nP P].

end

theory Classical:
	import Intuitionistic.
	assume excluded_middle: P ∈ Prop ⟹ P ∨ ¬P.
begin

	lemma prop_cases: if PQ: P ⟹ Q, nPQ: ¬P ⟹ Q, pP! P ∈ Prop, ! Q ∈ Prop then Q;
		apply or_elim[OF excluded_middle[OF pP]];
		- by PQ.
		- by nPQ.
		.

	lemma nnot_iff: if ! P ∈ Prop then ¬ ¬P ⟺ P;
		apply prop_cases[of P];
		- if P: P;
			unfold iff_true[OF P] not_true_iff iff_true[OF not_false].
		- if nP: ¬P;
			unfold not_imp_iff_false[OF nP] iff_true[OF not_false] not_true_iff.
		.

	lemma pierce_law: if PQP: (P ⟹ Q) ⟹ P, ! P ∈ Prop, ! Q ∈ Prop then P;
		apply prop_cases[of P];
		- if nP: ¬P;
			have f: false;
				by PQP[simp not_imp_iff_false[OF nP]].
			apply false_elim[OF f].
		.

end
