---
# Unrestricted Comprehension is Inconsistent
---
import Iff.
import Membership.
fix _Collect.
assume in_Collect_iff: x ∈ {x. P.[x]} ⟺ P.[x].
begin

theorem inconsistent: P;-- Any term is provable
	obtain R where R_def: x ∈ R ⟺ (x ∈ x ⟹ P);
		- for thesis if elim;
			apply abbrev[of (x. x ∈ x ⟹ P)];
			- for R if (simp);
				apply elim[of R].
			.
		.
	have RR_iff_nRR: R ∈ R ⟺ (R ∈ R ⟹ P);
		by R_def.
	have nRR: if RR: R ∈ R then P;
		by RR[unfold RR_iff_nRR] RR.
	have RR: R ∈ R;
		by nRR[fold RR_iff_nRR].
	by nRR[OF RR].

thy.
