-------
# Type-Free Logics
-------
begin

interpret Base.

theory Minimal:
	import TypeSafeMinimal.
	assume or_elim: if P ∨ Q, P ⟹ R, Q ⟹ R then R.
	assume ex_elim: if ∃x. P.[x], ∀x. P.[x] ⟹ Q then Q.
begin

	---
	## Disjunction
	---

	lemma or_iff: P ∨ Q ⟺ (∀R. (P ⟹ R) ⟹ (Q ⟹ R) ⟹ R);
		apply iff_intro[OF or_elim or_intro].

	interpret or: MetaSymmetric (∨);
		by #elim or_elim.

	---
	Algebraic properties of `(∨)`, with respect to `(⟺)`.
	Minimal logic does not allow `false` to be neutral of or: `false ∨ P ⟺ P`,
	because the `false` case does not derive `P`.
	---
	interpret or: iff.MetaCompatible (∨);
		- if PQ: P ⟺ Q, RS: R ⟺ S then P ∨ R ⟺ Q ∨ S;
			by iff_intro #elim or_elim #simp PQ RS.
		.
	note(cong) or.cong.

	interpret or: iff.MetaCommAbsorb (∨) true;
		by iff_intro[OF or.sym or.sym].

	interpret or: iff.MetaCommSemigroupAbsorb (∨) true;
		by iff_intro #elim or_elim #simp or_iff_true1 or_iff_true2.

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

	lemma ex_imp_all_imp: if ex: ∃x. P.[x] ⟹ Q, all: ∀x. P.[x] then Q;
		apply ex_elim[OF ex];
		- for x if imp: P.[x] ⟹ Q;
			by imp all.
		.

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
	theory ExRel:
		import ExRel.
	begin
		lemma ex_elim: if ex: ∃x < a. P.[x], imp: ∀x. x < a ⟹ P.[x] ⟹ Q then Q;
			apply ex[unfold ex_def, THEN ex_elim];
			- for x;
				by imp[of x].
			.
		lemma ex_cong_strong:
			if a: ∀x. x < a ⟺ x < a', P: ∀x. x < a' ⟹ (P.[x] ⟺ P'.[x])
			then (∃x < a. P.[x]) ⟺ (∃x < a'. P'.[x]);
			unfold+ ex_def a P.
		lemma ex_cong_weak:
			if P: ∀x. x < a ⟹ (P.[x] ⟺ P'.[x]) then (∃x < a. P.[x]) ⟺ (∃x < a. P'.[x]);
			unfold+ ex_def P.
		lemma ex_imp_iff: ((∃x < a. P.[x]) ⟹ Q) ⟺ (∀x. x < a ⟹ P.[x] ⟹ Q);
			apply iff_intro;
			- if imp, x: x < a, Px: P.[x];
				apply imp ex_intro1[OF x Px].
			- if all, ex;
				apply ex_elim[OF ex];
				- for x if x, Px;
					apply all[OF x Px].
				.
			.
		lemma ex_or_distrib: (∃x < a. P.[x] ∨ Q.[x]) ⟺ (∃x < a. P.[x]) ∨ (∃x < a. Q.[x]);
			simp ex_def and_or_distrib .ex_or_distrib.
	end

	theory AllExRel:
		import AllRel.
		import ExRel.
	begin
		lemma nex_iff_all_not: ¬(∃x < a. P.[x]) ⟺ (∀x < a. ¬ P.[x]);
			unfold ex_def all_def .nex_iff_all_not nand_iff_imp_not.
	end

	---
	The law of excluded middle `P ∨ ¬P` allows case analysis.
	It becomes classical logic if one assumes the law of explosion.
	---
	theory ExcludedMiddle:
		assume excluded_middle: P ∨ ¬P.
	begin

		lemma cases: if PQ: P ⟹ Q, nPQ: ¬P ⟹ Q then Q;
			apply or_elim[OF excluded_middle[of P]];
			- by PQ.
			- by nPQ.
			.

	end

	theory Choice:
		assume choice: (∀x. ∃y. P x y) ⟹ ∃f. ∀x. P x (f x).
	end

	theory ChoiceOperator:
		fix (SOME).
		assume ex_imp_SOME: (∃x. P.[x]) ⟹ P.[SOME x. P.[y]].
	end

end

---
Intuitionistic logic asserts the law of explosion `false ⟹ P`.
We can obtain such a `false` via `∀P. P`.
---
theory Intuitionistic:
	obtain false where false_elim(elim) if false then P;
		- for thesis if assm;
			apply assm[of (∀P. P)].
		.
	import Minimal.
begin

	lemma not_imp_iff_false: if nP: ¬P then P ⟺ false;
		by iff_intro not_imp_false[OF nP].

	lemma not_elim: if nP: ¬P, P: P then Q;
		use not_imp_false[OF nP P].

	lemma false_imp_iff(simp) (false ⟹ P) ⟺ true;
		by iff_true.

	interpret and: iff.MetaCommAbsorb (∧) false;
		by iff_intro.

	note(simp) and.left_absorb and.right_absorb.

	interpret or: iff.MetaCommNeutral (∨) false;
		by iff_intro or_intro #elim or_elim false_elim.

	note(simp) or.left_neutral or.right_neutral.

end

theory PierceLaw:
	assume pierce_law: if (P ⟹ Q) ⟹ P then P.
begin

end

---
We define classical logic as intuitionistic logic plus excluded middle.
---
theory Classical:
	import Intuitionistic.
	import ExcludedMiddle.
begin

	interpret PierceLaw;
		- if PQP: (P ⟹ Q) ⟹ P then P;
			apply cases[of P];
			- if nP: ¬P then P;
				apply PQP;
				- if P: P then Q;
					by not_elim[OF nP P].
				.
			.
		.

end

context Minimal begin

	---
	Double negation elimination alone will be classical logic.
	---
	theory DoubleNegationElimination:
		assume nnot_imp: if ¬¬P then P.
	begin

		lemma nnot_iff(simp) ¬¬P ⟺ P;
			apply iff_intro[OF nnot_imp nnot_intro].

		lemma contradiction: if not_imp: ¬P ⟹ false then P;
			apply nnot_imp;
			apply not_intro;
			by not_imp.

		interpret! Classical;
			retain false;
				- if 0: false then P;
					apply contradiction;
					by 0.
				.
			- then P ∨ ¬P;
				apply or_intro;
				- for Q if PQ: P ⟹ Q, nPQ: ¬ P ⟹ Q then Q;
					apply contradiction;
					- if nQ: ¬Q then false;
						have nP: ¬P;
							by not_intro not_imp_false[OF nQ] PQ.
						have P: P;
							apply contradiction;
							by not_imp_false[OF nQ] nPQ.
						by not_imp_false[OF nP P].
					.
				.
			.

end

---
Classical logic also implies double negation elimination.
---
context Classical begin
	interpret DoubleNegationElimination;
		- if nnP: ¬¬P then P;
			apply cases[of P];
			-.
			- if nP: ¬P;
				by not_elim[OF nnP nP].
			.
		.
end