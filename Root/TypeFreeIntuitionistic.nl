-------
# Type-Free Intuitionistic Logic
-------

base Root;

import True;
import False;

import TypeFreeMinimal;

finalize;

setup rewrite iff_elim1 iff_elim2 iff.refl iff.trans;
setup cong iff_cong_imp iff_cong_iff iff_cong_and iff_cong_not iff_cong_all iff_cong_or;

show not_imp_iff_false: if nP: ¬P then P ⟺ false :=
	apply iff_intro;
	- := by not_imp_false[OF nP];
	- := just false_elim;
	qed;

show false_imp_iff: (false ⟹ P) ⟺ true :=
	by iff_true[OF false_elim];

show false_and_iff: false ∧ P ⟺ false :=
	apply iff_intro;
	- := just and_elim1;
	- := just false_elim;
	qed;

show and_false_iff: P ∧ false ⟺ false :=
	unfold and_iff.commute;
	by false_and_iff;

show not_elim: if nP: ¬P, P: P then Q :=
	apply false_elim;
	by not_imp_false[OF nP P];
