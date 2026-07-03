---
# Russel's Paradox in Predicate Form
---
import Std, TypeFree, Minimal.
assume abbrev: ∀P. ∃p. ∀x. p x ⟺ P.[x].

begin

theorem Russel_paradox: ∃P. ¬(P ∨ ¬P);
	obtain R where R_def: R x ⟺ ¬ x x;
		- for thesis; apply abbrev[THEN ex_elim]>0.
		.
	apply ex_intro1[of (R R)] not_intro;
	- if or: R R ∨ ¬ R R;
		apply or_elim[OF or];
		- if RR: R R;
			by RR[unfold R_def] RR.
		- if nRR: ¬ R R;
			by nRR nRR[fold R_def].
		.
	.
