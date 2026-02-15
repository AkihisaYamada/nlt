import Membership.
import imp: Magma Prop (⟹).

begin

note! imp.closed.

theory And:
	import And.
	import and: Magma Prop (∧).
begin
	note! and.closed.
end

theory Iff:
	import Iff.
	import iff: Magma Prop (⟺).
begin
	note! iff.closed.
	interpret iff: Magmas (⟺).
	interpret iff_Prop: Equivalence Prop (⟺);
		-.
		- if xy: x ⟺ y; by iff.sym[OF xy].
		- if xy: x ⟺ y, yz: y ⟺ z; by iff.trans[OF xy yz].
		.
end

theory Not:
	import Not.
	import false: Member false Prop.
	import not: Unary (¬) Prop Prop.
begin
	note! false.closed not.closed.
end

theory TypeSafe:
	import .Iff.
	import .And.
	import .Not.
	obtain true where true_intro! true, ! true ∈ Prop;
		- for thesis if assm;
			apply assm[of (false ⟹ false)].
		.
	interpret TypeSafe.
	import Membership.
begin
	interpret and: iff_Prop.CommMonoid (∧) true;
		by and.commute and.left_assoc.
end

---
## Minimal Logic
---
theory Minimal:
	import TypeSafe.
	fix (∨).
	assume or_intro1: for P Q if P then P ∨ Q.
	assume or_intro2: for P Q if Q then P ∨ Q.
	assume or_elim: if P ∨ Q, R ∈ Prop, P ⟹ R, Q ⟹ R then R.
	import or: Magma Prop (∨).
begin
	note! or.closed.

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

	theory FirstOrder:
		fix QTYPE.
		assume all_type! if A ∈ QTYPE, ∀x. x ∈ A ⟹ P.[x] ∈ Prop then (∀x ∈ A. P.[x]) ∈ Prop.
		fix (∃∈).
		assume ex_intro1: if x ∈ A, P.[x] then ∃x ∈ A. P.[x].
		assume ex_elim: if ∃x ∈ A. P.[x], ∀x. x ∈ A ⟹ P.[x] ⟹ Q, Q ∈ Prop then Q.
		assume ex_type! if A ∈ QTYPE, ∀x. x ∈ A ⟹ P.[x] ∈ Prop then (∃x ∈ A. P.[x]) ∈ Prop.
	begin
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
			note(cong) in.all_cong_weak.
			simp not_iff_imp_false.

		lemma ex_or_distrib:
			if ! A ∈ QTYPE, ! ∀x. x ∈ A ⟹ P.[x] ∈ Prop, ! ∀x. x ∈ A ⟹ Q.[x] ∈ Prop
			then (∃x ∈ A. P.[x] ∨ Q.[x]) ⟺ (∃x ∈ A. P.[x]) ∨ (∃x ∈ A. Q.[x]);
		-	note(cong) in.all_cong_weak.
			simp iff_iff_and or_imp_iff in.all_and_distrib[dual];
			apply in.all_intro;
			- for x;
				by ex_intro1[of x].
			.
		.
		theory Impredicative:
			assume Prop_type: Prop ∈ QTYPE.
		end
	end

	theory SecondOrder:
		import FirstOrder.
		fix IND.
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
end

theory Intuitionistic:
	import Minimal.
	assume false_elim: if false, P ∈ Prop then P.
begin

	lemma not_imp_iff_false: if nP: ¬P, !P ∈ Prop then P ⟺ false;
		by iff_intro not_imp_false[OF nP] #elim false_elim.

	lemma false_imp_iff(simp) if ! P ∈ Prop then (false ⟹ P) ⟺ true;
		by iff_true #elim false_elim.

	interpret and: iff_Prop.CommMonoidAbsorb (∧) false true;
		by iff_intro #elim false_elim.

	interpret or: iff_Prop.CommMonoidAbsorb (∨) true false;
		by iff_intro #elim or_elim false_elim.

	note(simp) and.left_absorb and.right_absorb or.left_neutral or.right_neutral.

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
		-.
		- by PQ.
		- by nPQ.
		.

	lemma nnot_iff: if ! P ∈ Prop then ¬¬P ⟺ P;
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