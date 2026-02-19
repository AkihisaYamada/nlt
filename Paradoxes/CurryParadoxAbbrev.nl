---
# Unrestricted Abbreviation is Inconsistent
---
import Eq.
assume abbrev: for F if ∀f. (∀x. f x = F.[x]) ⟹ R then R.
begin

theorem inconsistent: P;-- Any term is provable
	obtain R where R_def: R x = (x x ⟹ P);
		- for thesis if assm;
			apply abbrev[of (x. x x ⟹ P)];
			- for R if (simp);
				apply assm[of R].
			.
		.
	have nRR: if RR: R R then P;
		by RR[unfold R_def] RR.
	have RR: R R;
		by nRR[fold R_def].
	by nRR[OF RR].

thy.
