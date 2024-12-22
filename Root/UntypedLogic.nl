----
# Untyped Logic
----

base Root;

import TypeFreeIntuitionistic;
import UntypedMinimalLogic;

ctxt;

setup conclude true_intro imp.refl iff.refl;

setup rewrite iff_elim1 iff.refl iff.trans;
setup dual iff.sym;

setup cong iff_cong_imp iff_cong_iff iff_cong_and iff_cong_or iff_cong_not iff_cong_all iff_cong_ex;

show false_or_iff: false ∨ P ⟺ P :=
	apply iff_intro;
	case or: false ∨ P :=
		apply or_elim[OF or];
		by false_elim imp.refl;
	by or_intro2;

show or_false_iff: P ∨ false ⟺ P :=
	apply iff_intro;
	case or: P ∨ false :=
		apply or_elim[OF or];
		by imp.refl false_elim;
	by or_intro1;


show not_or_imp_imp: if nPQ: ¬P ∨ Q, P: P then Q :=
	apply or_elim[OF nPQ];
	show! if nP: ¬P then Q :=
		by not_elim[OF nP P];
	show! if Q: Q then Q :=
		by Q;
	qed;


