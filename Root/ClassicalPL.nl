import IntuitionisticPL.

assume excluded_middle: P : prop ⟹ P ∨ ¬P.

begin

lemma prop_cases: if PQ: P ⟹ Q, nPQ: ¬P ⟹ Q, pP! P : prop, [Q : prop] then Q;
	apply or_elim[OF excluded_middle[OF pP]];
	-; by PQ.
	-; by nPQ.
	.

lemma nnot_iff: if [P : prop] then ¬¬P ⟺ P;
	apply prop_cases[of P];
	- if P: P;
		unfold+ iff_true[OF P] not_true_iff not_false_iff.
	- if nP: ¬P;
		apply iff_intro;
		- if nnP: ¬¬P;
			apply not_elim[OF nnP nP].
		by nnot_intro.
	.

lemma pierce_law: if PQP: (P ⟹ Q) ⟹ P, [P : prop, Q : prop] then P;
	apply prop_cases[of P];
	- .
	- if nP: ¬P;
		have f: false;
			by PQP[unfolded+ not_imp_iff_false[OF nP] false_imp_iff true_imp_iff].
		apply false_elim[OF f].
	.

