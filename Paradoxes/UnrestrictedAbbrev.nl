---
# Unrestricted Abbreviation is Inconsistent
---
import Std, Eq.
assume abbrev: for F if ∀f. (∀x. f x = F.[x]) ⟹ P then P.
begin

theorem inconsistent: false;-- Any term is provable
	obtain R where R_def: R x = (x x ⟹ false);
		- for thesis; apply abbrev>0.
		.
	have nRR: if RR: R R then false;
		by RR[unfold R_def] RR.
	have RR: R R;
		by nRR[fold R_def].
	by nRR[OF RR].
