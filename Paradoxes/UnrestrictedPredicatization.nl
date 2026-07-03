---
# Unrestricted Predicatization is Inconsistent

It is unsafe to assume that any term `P.[x]` with free variable `x` can be
represented by a predicative form such that `p x` if and only if `P.[x]`.
This is exemplified by Curry's paradox.
Under equality, the same inconsistency arises for unrestricted abbreviation.
---

import Std, Iff.
assume abbrev: for P if ∀p. (∀x. p x ⟺ P.[x]) ⟹ Q then Q.

begin

theorem inconsistent: false;-- Any term is provable
	obtain R where R_def: R x ⟺ (x x ⟹ false);
		- for thesis; apply abbrev>0.
		.
	have nRR: if RR: R R then false;
		by RR[unfold R_def] RR.
	have RR: R R;
		by nRR[fold R_def].
	by nRR[OF RR].
