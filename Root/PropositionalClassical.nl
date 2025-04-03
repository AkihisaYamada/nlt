import PropositionalIntuitionistic.

assume excluded_middle: prop P ⟹ P ∨ ¬P.

begin

setup rewrite iff_imp iff_imp_rev iff.refl iff.trans.
setup dual iff.sym.

lemma prop_cases: if PQ: P ⟹ Q, nPQ: ¬P ⟹ Q, pP! prop P, [prop Q] then Q;
	apply or_elim[OF excluded_middle[OF pP]];
	- by PQ.
	- by nPQ.
	.

lemma nnot_iff: if [prop P] then ¬¬P ⟺ P;
	apply prop_cases(P);
	- if P: P;
		unfold+ iff_true[OF P] not_true_iff not_false_iff.
	- if nP: ¬P;
		apply iff_intro;
		- if nnP: ¬¬P;
			apply not_elim[OF nnP nP].
		by nnot_intro.
	.

lemma pierce_law: if PQP: (P ⟹ Q) ⟹ P, [prop P, prop Q] then P;
	apply prop_cases(P);
	- .
	- if nP: ¬P;
		have f: false;
			by PQP[unfolded+ not_imp_iff_false[OF nP] false_imp_iff true_imp_iff].
		apply false_elim[OF f].
	.

