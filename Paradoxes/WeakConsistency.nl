fix ⊤.
assume app_top: f ⊤.

lemma top: ⊤;
	have imp_top: (∀x. x ⟹ x) ⟹ ⊤;
		apply app_top.
	apply imp_top.

import Std, Iff.

theorem inconsistent: false;
	have iff: false ⟺ ⊤;
		by app_top.
	unfold iff;
	by top.
