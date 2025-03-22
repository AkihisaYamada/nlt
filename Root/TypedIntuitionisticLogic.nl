------
# Typed Intuitionistic Logic
------

base Root.

import TypedMinimalLogic.
import PropositionalIntuitionistic.

begin

setup rewrite iff_imp iff_imp_rev iff.refl iff.trans.
setup dual iff.sym.

lemma ex_false_iff: (∃x:ι. false) ⟺ false;
	by not_imp_iff_false nex_false.
