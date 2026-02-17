---
# Russel's Paradox in Predicate Form
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



