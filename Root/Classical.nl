---
# Classical Logic

Classical logic assumes excluded middle `P ∨ ¬P`,
and Russel's paradox says one must restrict what `P` are.
So we start with Propositional Logic and assume excluded middle for `Prop`.
---
import Intuitionistic.
import Propositional.

assume excluded_middle: P ∈ Prop ⟹ P ∨ ¬P.

begin

lemma prop_cases: if PQ: P ⟹ Q, nPQ: ¬P ⟹ Q, pP! P ∈ Prop, [Q ∈ Prop] then Q;
	apply or_elim[OF excluded_middle[OF pP]];
	-; by PQ.
	-; by nPQ.
	.

lemma nnot_iff: if [P ∈ Prop] then ¬¬P ⟺ P;
	apply prop_cases[of P];
	- if P: P;
		unfold iff_true[OF P] not_true_iff iff_true[OF not_false].
	- if nP: ¬P;
		unfold not_imp_iff_false[OF nP] iff_true[OF not_false] not_true_iff.
	.

lemma pierce_law: if PQP: (P ⟹ Q) ⟹ P, [P ∈ Prop, Q ∈ Prop] then P;
	apply prop_cases[of P];
	- if nP: ¬P;
		have f: false;
			by PQP[unfolded not_imp_iff_false[OF nP] false_imp_iff true_imp_iff].
		apply false_elim[OF f].
	.
