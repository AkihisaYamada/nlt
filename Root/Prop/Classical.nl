import Intuitionistic.

assume excluded_middle: P ∈ PROP ⟹ P ∨ ¬P.

begin

lemma prop_cases: if PQ: P ⟹ Q, nPQ: ¬P ⟹ Q, pP! P ∈ PROP, [Q ∈ PROP] then Q;
	apply or_elim[OF excluded_middle[OF pP]];
	- by PQ.
	- by nPQ.
	.

lemma nnot_iff: if [P ∈ PROP] then ¬¬P ⟺ P;
	apply prop_cases[of P];
	if P: P;
		unfold P not_true_iff not_false.
	if nP: ¬P;
		unfold not_imp_iff_false[OF nP] not_false not_true_iff.
	.

lemma pierce_law: if PQP: (P ⟹ Q) ⟹ P, [P ∈ PROP, Q ∈ PROP] then P;
	apply prop_cases[of P];
	if nP: ¬P;
		have f: false;
			by PQP[unfolded not_imp_iff_false[OF nP] false_imp_iff true_imp_iff].
		apply false_elim[OF f].
	.

