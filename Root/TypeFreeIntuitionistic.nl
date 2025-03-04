-------
# Type-Free Intuitionistic Logic
-------

base Root;

import True;
import False;

import TypeFreeMinimal;

finalize;

setup rewrite iff_elim1 iff_elim2 iff.refl iff.trans;
setup dual iff.sym;

lemma not_imp_iff_false: if nP: ¬P then P ⟺ false :=
	apply iff_intro;
	- by not_imp_false[OF nP];
	- just false_elim;
	done;

lemma false_imp_iff: (false ⟹ P) ⟺ true :=
	by iff_true[OF false_elim];

lemma false_and_iff: false ∧ P ⟺ false :=
	apply iff_intro;
	- just and_elim1;
	- just false_elim;
	done;

lemma and_false_iff: P ∧ false ⟺ false :=
	unfold and_iff.commute;
	by false_and_iff;

lemma not_elim: if nP: ¬P, P: P then Q :=
	apply false_elim;
	by not_imp_false[OF nP P];
