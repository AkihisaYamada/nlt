------
# Quantified Intuitionistic Logic
------

fix (¬) (∧) (∨) (⟺) (∀∋) (∃∋).

import ..Intuitionistic.
import Minimal.

begin

lemma ex_false_iff: A ∈ TYPE ⟹ (∃x ∈ A. false) ⟺ false;
	by not_imp_iff_false nex_false.
