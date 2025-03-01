------
# Typed Classical Logic
------

base Root;

import TypedIntuitionisticLogic;

assume excluded_middle: prop P ⟹ P ∨ ¬P;

finalize;

setup rewrite iff_imp iff_imp_rev iff.refl iff.trans;
setup dual iff.sym;
setup cong iff_cong_imp iff_cong_iff iff_cong_all iff_cong_not iff_cong_and iff_cong_or;

lemma prop_cases: if PQ: P ⟹ Q, nPQ: ¬P ⟹ Q, pP: prop P, [prop Q] then Q :=
	apply or_elim[OF excluded_middle[OF pP]];
	- if [P] := by PQ;
	- if [¬P] := by nPQ;
	by pP;

lemma nnot_iff: if [prop P] then ¬¬P ⟺ P :=
	apply prop_cases(P);
	- if P: P :=
		unfold+ iff_true[OF P] not_true_iff not_false_iff;
		done;
	- if nP: ¬P :=
		apply iff_intro;
		- if nnP: ¬¬P :=
			apply not_elim[OF nnP nP];
			done;
		by nnot_intro;
	done;

lemma pierces_law: if [prop P, prop Q] then ((P ⟹ Q) ⟹ P) ⟹ P :=
	apply prop_cases(P);
	- if P: P :=
		unfold+ iff_true[OF P] imp_true_iff;
		by true_intro;
	- if nP: ¬P :=
		unfold+ not_imp_iff_false[OF nP] false_imp_iff true_imp_iff;
		done;
	done;

