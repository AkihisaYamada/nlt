------
# Typed Classical Logic
------

base Propositional;

import ExcludedMiddle;

finalize;

setup rewrite iff_elim1 iff.refl iff.trans;
setup dual iff.sym;
setup cong iff_cong_imp iff_cong_iff iff_cong_and iff_cong_not;

setup conclude imp.refl iff.refl true_intro;

show prop_cases: if pP: prop P, pQ: prop Q, PQ: P ⟹ Q, nPQ: ¬P ⟹ Q then Q :=
	apply or_elim[OF excluded_middle[OF pP]];
	apply+ prop_imp_intro not.type pP pQ;
	by PQ nPQ;

show nnot_iff: if pP: prop P then ¬¬P ⟺ P :=
	apply prop_cases[OF pP];
	apply+ iff.type not.type pP;
	case P: P :=
		unfold+ iff_true[OF P] not_true_iff not_false_iff;
		by iff.refl;
	case nP: ¬P :=
		apply iff_intro;
		case nnP: ¬¬P :=
			by not_elim[OF nnP nP pP];
		by nnot_intro;
	qed;

show pierces_law: if pP: prop P, pQ: prop Q then ((P ⟹ Q) ⟹ P) ⟹ P :=
	apply prop_cases[OF pP];
	apply+ prop_imp_intro pP pQ;
	note! pQ;
	note! pP;
	note! pP;
	case P: P :=
		unfold+ iff_true[OF P] imp_true_iff;
		by true_intro;
	case nP: ¬P :=
		unfold+ not_imp_iff_false[OF nP pP] false_imp_iff[OF pQ] true_imp_iff;
		done;
	qed;

