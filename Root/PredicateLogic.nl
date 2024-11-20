base Root;

import IntuitionisticLogic;

import Ex;

setup rewrite iff.refl iff.sym iff.trans iff_elim1;
setup cong
	iff_cong_imp: P ⟹ Q,
	iff_cong_iff: P ⟺ Q,
	iff_cong_and: P ∧ Q,
	iff_cong_or: P ∨ Q,
	iff_cong_not: ¬P,
	iff_cong_defined: defined P;

setup conclude imp.refl iff.refl true_intro;
