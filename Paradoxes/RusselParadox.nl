---
# Russel's Paradox
---
import TypeFree.
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
			by not_imp_false[OF 1[unfold RR_iff_not_RR] 1].
		- if 0: ¬ R ∈ R;
			by not_imp_false[OF 0 0[fold RR_iff_not_RR]].
		.
	.
