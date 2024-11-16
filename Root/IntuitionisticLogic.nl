base Root;

import False;

import MinimalLogic;

setup rewrite iff.refl iff.sym iff.trans iff_elim1;
setup cong
	P ⟹ Q: iff_cong_imp,
	P ⟺ Q: iff_cong_iff,
	P ∧ Q: iff_cong_and,
	P ∨ Q: iff_cong_or,
	¬P: iff_cong_not,
	defined P: iff_cong_defined;

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

show not_or_imp_imp: if nPQ: ¬P ∨ Q, P: P then Q;
	apply or_elim[OF nPQ];
	show! if nP: ¬P then Q;
		by not_elim[OF nP P];
	show! if Q: Q then Q;
		by Q;
	qed;

show imp_defined: if P: defined P, Q: defined Q then defined (P ⟹ Q);
	apply defined_elim[OF P];
	case P: P;
		apply defined_elim[OF Q];
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

show iff_defined: if dP: defined P, dQ: defined Q then defined (P ⟺ Q);
	unfold iff_iff_and;
	apply and_defined;
	by imp_defined[OF dP dQ], imp_defined[OF dQ dP];


