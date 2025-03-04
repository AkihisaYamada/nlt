base Root;

import PropositionalMinimal;

assume false_elim: false ⟹ prop P ⟹ P;

finalize;

setup rewrite iff_imp iff_imp_rev iff.refl iff.trans;
setup dual iff.sym;

lemma not_imp_iff_false: if nP: ¬P, [prop P] then P ⟺ false :=
	apply iff_intro;
	- by not_imp_false[OF nP];
	- if f: false :=
		apply false_elim[OF f];
		done;
	done;

lemma false_imp_iff: if [prop P] then (false ⟹ P) ⟺ true :=
	apply iff_true;
	- if f: false :=
		apply false_elim[OF f];
		done;
	done;

lemma false_and_iff: if [prop P] then false ∧ P ⟺ false :=
	apply iff_intro;
	- if and: false ∧ P :=
		by and_elim1[OF and];
	- if f: false :=
		apply false_elim[OF f];
		done;
	done;

lemma and_false_iff: if [prop P] then P ∧ false ⟺ false :=
	unfold and_iff.commute;
	by false_and_iff;

lemma not_elim: if nP: ¬P, P: P, [prop P, prop Q] then Q :=
	apply false_elim;
	by not_imp_false[OF nP P];
