---
# Unrestricted Abbreviation is Inconsistent
---
import Eq.
assume abbrev: for F if ∀f. (∀x. f x = F.[x]) ⟹ R then R.
begin

theorem inconsistent: P;-- Any term is provable
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
		by RR[unfold RR_eq_nRR] RR.
	have RR: R R;
		by nRR[fold RR_eq_nRR].
	by nRR[OF RR].

thy.
