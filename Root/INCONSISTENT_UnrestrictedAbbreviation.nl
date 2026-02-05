---
# Unrestricted Abbreviation is Inconsistent
---
import Eq.
assume abbrev: if ∀f. (∀x. f x = F.[x]) ⟹ R then R.
begin

theorem Curry_paradox_eq: P;-- Any term is provable
	obtain R where R_def: R x = (x x ⟹ P);
		- for thesis if elim;
			apply abbrev[of (x. x x ⟹ P)];
			- for R if (simp);
				apply elim[of R].
			.
		.
	have RR_eq_nRR: R R = (R R ⟹ P);
		by R_def.
	have nRR: if RR: R R then P;
		by RR[unfolded RR_eq_nRR] RR.
	have RR;
		by nRR[folded RR_eq_nRR].
	by nRR[OF RR].


