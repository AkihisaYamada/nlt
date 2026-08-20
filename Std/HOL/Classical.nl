---
# Classical HOL
---
assume nnot_elim_axiom: ∀P : Prop. ¬ ¬ P ⟶ P.
begin

	instance Prop.Classical;
		- if nnP: ¬ ¬ P, ... then P;
			apply nnot_elim_axiom[THEN all_elim1[of P], THEN imp_elim1]; by nnP.
		.

end
