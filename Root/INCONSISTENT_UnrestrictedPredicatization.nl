---
# Unrestricted Predicatization is Inconsistent

It is unsafe to assume that any term `P.[x]` with free variable `x` can be
represented by a predicative form such that `p x` if and only if `P.[x]`.
This is exemplified by Curry's paradox.
Under equality, the same inconsistency arises for unrestricted abbreviation.
---
import TypeFree.
import Minimal.
assume abbrev: ∀P. ∃p. ∀x. p x ⟺ P.[x].

begin

---
The core ingredient is as in Russel's paradox, which says it is inconsistent
to assume excluded middle `P ∨ ¬P` unrestrictedly.
---
obtain R where R_def: R x ⟺ (¬ x x);
	- for thesis if elim;
		apply abbrev[of (x. ¬ x x), THEN ex_elim];
		- for R if (simp);
			apply elim[of R].
		.
	.
lemma RR_iff_not_RR: R R ⟺ (¬ R R);
	by R_def.

theorem Russel_paradox: ∃P. ¬(P ∨ ¬P);
	apply ex_intro1[of (R R)] not_intro;
	- if or: R R ∨ ¬ R R;
		apply or_elim[OF or];
		- if RR: R R;
			have nRR: ¬ R R;
				fold RR_iff_not_RR;
				by RR.
			by not_imp_false[OF nRR RR].
		- if nRR: ¬ R R;
			have RR: R R;
				by nRR[fold RR_iff_not_RR].
			by not_imp_false[OF nRR RR].
		.
	.

---
Curry's paradox more critically demonstrates it is inconsistent: any term is provable.
---
lemma Curry_paradox_false: false;
	have nRR: ¬ R R;
		apply not_intro;
		- if RR: R R;
			have nRR: ¬ R R;
				fold RR_iff_not_RR;
				by RR.
			by not_imp_false[OF nRR RR].
		.
	apply not_imp_false[OF nRR];
	by nRR[fold RR_iff_not_RR].

---
Since minimal logic does not put any assumption on `false`, one can instantiate `false` to any term.
---
theorem Curry_paradox: P;
	interpret P: INCONSISTENT_UnrestrictedPredicatization;
		obtain notP where
			not_intro: if Q ⟹ P then notP Q,
			not_imp_false: if notP Q, Q then P;
			- for thesis if assm;
				apply abbrev[of (x. x ⟹ P), THEN ex_elim];
				- for notP if (simp);
					apply assm[of notP].
				.
			.
		instantiate false := P, (¬) := notP.
		.
	by P.Curry_paradox_false.

thy.
