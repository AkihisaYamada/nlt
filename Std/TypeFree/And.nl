---
## Primitive Specification of Conjunction
---
fix (∧).
assume and_intro! for P Q if P, Q then P ∧ Q.
assume and_elim1: if P ∧ Q then P.
assume and_elim2: if P ∧ Q then Q.

begin

lemma and_elim#elim if PQ: P ∧ Q, PQR: P ⟹ Q ⟹ R then R;
	by PQR and_elim1[OF PQ] and_elim2[OF PQ].

lemma and_imp_intro: if PQR: P ⟹ Q ⟹ R, PQ: P ∧ Q then R;
	by and_elim[OF PQ PQR].

interpret and: MetaPartialEquivalence (∧).

extend Not begin

	extend ContraPos begin

		lemma nand_intro1: if nP: ¬ P then ¬ (P ∧ Q);
			apply not.cmono[OF and_elim1];
			by nP.

		lemma nand_intro2: if nQ: ¬ Q then ¬ (P ∧ Q);
			apply not.cmono[OF and_elim2];
			by nQ.

	end

	extend MinimalNot begin

		lemma not_contradiction: ¬ (P ∧ ¬P);
			apply imp_not_imp_not;
			by #elim not_elim_not.

	end

end


extend Iff begin

	interpret? And;
		by iff_intro.

end
