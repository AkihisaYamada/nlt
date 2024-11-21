------
# Typed Classical Logic
------

base Root;

import TypedIntuitionisticLogic;

import ExcludedMiddle;

setup rewrite iff.refl iff.sym iff.trans iff_elim1;
setup cong
	iff_cong_imp: P ⟹ Q,
	iff_cong_iff: P ⟺ Q,
	iff_cong_and: P ∧ Q,
	iff_cong_not: ¬P;

setup conclude imp.refl iff.refl true_intro;

show prop_cases: if pP: prop P, pQ: prop Q, PQ: P ⟹ Q, nPQ: ¬P ⟹ Q then Q;
	apply or_elim[OF excluded_middle[OF pP]];
	apply+ imp.type not.type pP pQ;
	by PQ nPQ;

show nnot_iff: if pP: prop P then ¬¬P ⟺ P;
	apply prop_cases[OF pP];
	apply+ iff.type not.type pP;
	case P: P;
		unfold+ iff_true[OF P] not_true_iff not_false_iff;
		by iff.refl;
	case nP: ¬P;
		apply iff_intro;
		case nnP: ¬¬P;
			by not_elim[OF nnP nP];
		by nnot_intro;
	qed;

show pierces_law: if pP: prop P, pQ: prop Q then ((P ⟹ Q) ⟹ P) ⟹ P;
	apply prop_cases[OF pP];
	apply+ imp.type pP pQ;
	case P: P;
		unfold+ iff_true[OF P] imp_true_iff;
		by true_intro;
	case nP: ¬P;
		unfold+ not_imp_iff_false[OF nP] false_imp_iff true_imp_iff;
		by true_intro;
	qed;

