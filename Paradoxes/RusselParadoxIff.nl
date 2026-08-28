---
# Russel's Paradox
---
import Std, Minimal.
fix (∈) Collect.
syntax { _ . _ } := Collect.
assume in_Collect_iff: x ∈ {x. P.[x]} ⟺ P.[x].

begin

theorem Russel_paradox: ∃P. ¬(P ∨ ¬P);
	obtain R where R_def: x ∈ R ⟺ ¬ x ∈ x;
		- for thesis if assm;
			apply assm[of {x. ¬ x ∈ x}];
			unfold in_Collect_iff.
		.
	apply ex_intro1[of (R ∈ R)], imp_not_imp_not;
	- if or: R ∈ R ∨ ¬ R ∈ R;
		apply or_elim[OF or];
		- if RR: R ∈ R;
			by not_elim_not[OF RR[unfold R_def] RR].
		- if nRR: ¬ R ∈ R;
			by not_elim_not[OF nRR nRR[fold R_def]].
		.
	.
