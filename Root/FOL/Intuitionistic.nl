------
# Quantified Intuitionistic Logic
------

import ..Intuitionistic.

begin

interpret Minimal.

lemma ex_false_iff: A ∈ TYPE ⟹ (∃x ∈ A. false) ⟺ false;
	by not_imp_iff_false nex_false.
