fix (∧).
import and: Magma Prop (∧).
assume and_intro! if P, Q, P : Prop, Q : Prop then P ∧ Q.
assume and_elim1: if P ∧ Q, P : Prop, Q : Prop then P.
assume and_elim2: if P ∧ Q, P : Prop, Q : Prop then Q.

begin

note! and.closed.

lemma and_elim#elim if PQ: P ∧ Q, PQR: P ⟹ Q ⟹ R, [P : Prop, Q : Prop] then R;
	by PQR and_elim1[OF PQ] and_elim2[OF PQ].

lemma and_imp_intro: if PQR: P ⟹ Q ⟹ R, PQ: P ∧ Q, [P : Prop, Q : Prop] then R;
	by and_elim[OF PQ PQR].

interpret and: PartialEquivalence Prop (∧).

extend Not begin

	extend ContraPos begin

		lemma nand_intro1: if nP: ¬ P, [P : Prop, Q : Prop] then ¬ (P ∧ Q);
			apply not_imp_imp_not[OF nP];
			by nP.

		lemma nand_intro2: if nQ: ¬ Q, [P : Prop, Q : Prop] then ¬ (P ∧ Q);
			apply not_imp_imp_not[OF nQ];
			by nQ.

	end

	extend MinimalNot begin

		lemma not_contradiction: if [P : Prop] then ¬ (P ∧ ¬P);
			apply imp_not_imp_not;
			by #elim not_elim_not.

	end

end
