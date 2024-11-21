base Root;

import UntypedLogic;

setup rewrite iff.refl iff.sym iff.trans iff_elim1;
setup cong
	iff_cong_imp: P ⟹ Q,
	iff_cong_iff: P ⟺ Q,
	iff_cong_and: P ∧ Q,
	iff_cong_or: P ∨ Q,
	iff_cong_not: ¬P;

setup conclude imp.refl iff.refl true_intro;

fix defined;
assume defined_iff: defined P ⟺ P ∨ ¬P;

interpret defined: ExcludedMiddle {
	for defined _ _;
	discharge if dP: defined P then P ∨ ¬P;
		by dP[unfolded defined_iff];
}

note defined_elim: for P R, if dP: defined P then or_elim[OF dP[unfolded defined_iff]];

show imp_defined: if P: P then defined P;
	unfold defined_iff;
	by or_intro1[OF P];

interpret defined.true: Member {
	for defined true;
	discharge defined true;
		apply imp_defined;
		done;
}

show not_imp_defined: if P: ¬P then defined P;
	unfold defined_iff;
	by or_intro2[OF P];

show defined_intro: if 1: ∀Q. (P ⟹ Q) ⟹ (¬P ⟹ Q) ⟹ Q then defined P;
	unfold defined_iff;
	by or_intro[OF 1];

show defined_elim: if P: defined P then (P ⟹ Q) ⟹ (¬P ⟹ Q) ⟹ Q;
	by or_elim[OF P[unfolded defined_iff]];

show nnot_defined: ¬¬ defined P;
	unfold defined_iff;
	by nnot_excluded_middle;

interpret defined.imp: Magma {
	for defined (⟹);
	discharge if dP: defined P, dQ: defined Q then defined (P ⟹ Q);
		apply defined_elim[OF dP];
		case P: P;
			apply defined_elim[OF dQ];
			case Q: Q;
				by imp_defined[OF weaken[OF Q]];
			case nQ: ¬Q;
				apply not_imp_defined;
				by imp_not[OF P nQ];
			qed;
		case nP: ¬P;
			apply imp_defined;
			by not_elim[OF nP];
		qed;
}
interpret defined.and: Magma {
	for defined (∧);
	discharge if dP: defined P, dQ: defined Q then defined (P ∧ Q);
		apply defined_elim[OF dP];
		case P: P;
			apply defined_elim[OF dQ];
			case Q: Q;
				apply imp_defined;
				by and_intro[OF P Q];
			case nQ: ¬Q;
				apply not_imp_defined;
				by nand_intro2[OF nQ];
			qed;
		case nP: ¬P;
			apply not_imp_defined;
			by nand_intro1[OF nP];
		qed;
}

interpret defined.or: Magma {
	for defined (∨);
	discharge if dP: defined P, dQ: defined Q then defined (P ∨ Q);
		apply defined_elim[OF dP];
		case P: P;
			by imp_defined[OF or_intro1[OF P]];
		case nP: ¬P;
			apply defined_elim[OF dQ];
			case Q: Q;
				by imp_defined[OF or_intro2[OF Q]];
			case nQ: ¬Q;
				apply not_imp_defined;
				unfold nor_iff_and;
				by and_intro[OF nP nQ];
			qed;
		qed;
}

interpret defined: ClassicalLogic {
	for defined;
	retain;
	retain;
	for (∧);
	know;
	know;
	know;
	for (∨);
	know;
	know;
	know;
	for (⟺);
	know;
	know;
	know;
	for (¬);
	know;
	know;


	discharge defined true;
		by imp_defined[OF true_intro];

	discharge defined false;
		by not_imp_defined[OF not_false];


	discharge if dP: defined P then defined (¬P);
		apply defined_elim[OF dP];
		case P: P;
			apply not_imp_defined;
			by nnot_intro[OF P];
		by imp_defined;

	discharge if PQ: P ⟺ Q then defined P ⟺ defined Q;
		unfold+ defined_iff PQ;
		by iff.refl;

}


setup cong defined.iff_cong_prop: defined P;

thm defined.nnot_iff;