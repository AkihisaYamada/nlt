base Root;

import False;

import MinimalLogic;

setup rewrite iff.refl iff.sym iff.trans iff_elim1;
setup cong
	P ⟹ Q: iff_cong_imp,
	P ⟺ Q: iff_cong_iff,
	P ∧ Q: iff_cong_and,
	P ∨ Q: iff_cong_or,
	¬P: iff_cong_not;
setup conclude imp.refl iff.refl true_intro;

show false_imp_iff: (false ⟹ P) ⟺ true;
	by iff_true[OF false_elim];

show false_and_iff: false ∧ P ⟺ false;
	apply iff_intro;
	show! if fP: false ∧ P then false;
		by and_elim1[OF fP];
	show! if f: false then false ∧ P;
		by false_elim[OF f];
	qed;

show and_false_iff: P ∧ false ⟺ false;
	unfold and_commute;
	by false_and_iff;

show not_elim: if nP: ¬P, P: P then Q;
	show f: false;
		by not_imp_false[OF nP P];
	by false_elim[OF f];

show nnand_iff: ¬¬(P ∧ Q) ⟺ ¬¬P ∧ ¬¬Q;
	apply iff_intro;
	note! nnand_imp_nnot_and_nnot;
	show! if and: ¬¬P ∧ ¬¬Q then ¬¬(P ∧ Q);
		apply not_intro;
		assume nand: ¬(P ∧ Q);
		show 1: if P: P, Q: Q then false;
		show! false;
