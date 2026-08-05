---
## Propositional Minimal Logic
---

assume and_intro! if P, Q, P ∈ Prop, Q ∈ Prop then P ∧ Q.
assume and_elim1: if P ∧ Q, P ∈ Prop, Q ∈ Prop then P.
assume and_elim2: if P ∧ Q, P ∈ Prop, Q ∈ Prop then Q.

begin

lemma and_elim: if PQ: P ∧ Q, PQR: P ⟹ Q ⟹ R, ! P ∈ Prop, ! Q ∈ Prop, ! R ∈ Prop then R;
	by PQR and_elim1[OF PQ] and_elim2[OF PQ].

lemma and_imp_intro: if PQR: P ⟹ Q ⟹ R, PQ: P ∧ Q, ! P ∈ Prop, ! Q ∈ Prop, ! R ∈ Prop then R;
	by and_elim[OF PQ PQR].

interpret and: PartialEquivalence Prop (∧).



