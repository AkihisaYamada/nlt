base Root;

obtain false where false_elim: ∀P. false ⟹ P;
	fix thesis;
	assume assm: ∀false. (∀P. false ⟹ P) ⟹ thesis;
	show 1: (∀x. x) ⟹ P;
		assume 2: ∀x. x;
		by 2(P);
	by assm(∀P. P)[OF 1];

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

