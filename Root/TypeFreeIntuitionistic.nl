-------
# Type-Free Part of Intuitionistic Logic
-------

base Root;

import True;
import False;

import TypeFreeMinimal;

setup rewrite iff.refl iff.sym iff.trans iff_elim1;
setup cong
	iff_cong_imp: P ⟹ Q,
	iff_cong_iff: P ⟺ Q,
	iff_cong_and: P ∧ Q,
	iff_cong_not: ¬P,
	iff_cong_all! ∀x. α.[x];

setup conclude imp.refl iff.refl true_intro;

show not_imp_iff_false: if nP: ¬P then P ⟺ false;
	apply iff_intro;
	case P: P;
		by not_imp_false[OF nP P];
	case f: false;
		by false_imp[OF f];
	qed;

show false_imp_iff: (false ⟹ P) ⟺ true;
	by iff_true[OF false_imp];

show false_and_iff: false ∧ P ⟺ false;
	apply iff_intro;
	show! if fP: false ∧ P then false;
		by and_elim1[OF fP];
	show! if f: false then false ∧ P;
		by false_imp[OF f];
	qed;

show and_false_iff: P ∧ false ⟺ false;
	unfold and_commute;
	by false_and_iff;

show not_elim: if nP: ¬P, P: P then Q;
	show f: false;
		by not_imp_false[OF nP P];
	by false_imp[OF f];

