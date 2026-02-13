---
# Unrestricted Comprehension is Inconsistent

---
import Minimal.
import Membership.
fix _Collect.
assume in_Collect_iff: x ∈ {x. P.[x]} ⟺ P.[x].

begin

obtain R where R_def: x ∈ R ⟺ ¬ x ∈ x;
	- for thesis if assm;
		apply assm[of {x. ¬ x ∈ x}];
		unfold in_Collect_iff.
	.
lemma RR_iff_not_RR: R ∈ R ⟺ (¬ R ∈ R);
	by R_def.

theorem Russel_paradox: ∃X x. ¬(x ∈ X ∨ ¬ x ∈ X);
	apply+ ex_intro1[of R] and_intro not_intro;
	- if or: R ∈ R ∨ ¬ R ∈ R then false;
		apply or_elim[OF or];
		- if 1: R ∈ R;
			by not_imp_false[OF 1[unfolded RR_iff_not_RR] 1].
		- if 0: ¬ R ∈ R;
			by not_imp_false[OF 0 0[folded RR_iff_not_RR]].
		.
	.
theorem Curry_paradox: false;
	have nRR: ¬ R ∈ R;
		apply not_intro;
		- if RR: R ∈ R;
			have nRR: ¬ R ∈ R;
				fold RR_iff_not_RR;
				by RR.
			by not_imp_false[OF nRR RR].
		.
	apply not_imp_false[OF nRR];
	by nRR[folded RR_iff_not_RR].
