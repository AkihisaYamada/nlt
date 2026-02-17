---
# Unrestricted Predicatization is Inconsistent

It is unsafe to assume that any term `P.[x]` with free variable `x` can be
represented by a predicative form such that `p x` if and only if `P.[x]`.
This is exemplified by Curry's paradox.
Under equality, the same inconsistency arises for unrestricted abbreviation.
---

import Iff.
assume abbrev: for P if ∀p. (∀x. p x ⟺ P.[x]) ⟹ Q then Q.

begin

theorem inconsistent: P;-- Any term is provable
	obtain R where R_def: R x ⟺ (x x ⟹ P);
		- for thesis if assm;
			apply abbrev[of (x. x x ⟹ P)];
			- for R if (simp);
				apply assm[of R].
			.
		.
	have RR_iff_nRR: R R ⟺ (R R ⟹ P);
		by R_def.
	have nRR: if RR: R R then P;
		by RR[unfold RR_iff_nRR] RR.
	have RR: R R;
		by nRR[fold RR_iff_nRR].
	by nRR[OF RR].

thy.

end
