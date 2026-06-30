---
# Russel's Paradox
---
import Std.
import Eq.
import TypeFree.
import Minimal.
fix (∈) Collect.
syntax {_. _} := Collect.
assume in_Collect_iff: x ∈ {x. P.[x]} ⟺ P.[x].

begin

theorem Russel_paradox: ∃P. ¬(P ∨ ¬P);
	define R = {x. ¬ x ∈ x}.
	have RR_iff_nRR: R ∈ R ⟺ ¬ R ∈ R;
		unfold[at 0 0 1] R_def; simp in_Collect_iff.
	apply ex_intro1[of (R ∈ R)];
	-> if or: R ∈ R ∨ ¬ R ∈ R then false;
		apply or_elim[OF or];
		- if RR: R ∈ R;
			by RR[unfold RR_iff_nRR] RR.
		- if nRR: ¬ R ∈ R;
			by nRR nRR[fold RR_iff_nRR].
		.
	.
