---
## Classical Logic Based on Equality and Negation

By having equality and negation as primitives, one can "define" other logical connectives.
One nice fact of this formulation is that when propositions are assumed to be closed under
implication and negation, then derived operators can be proved to close in propositions.
One drawback is that it is stronger than purely logical axiomatizations, when multivalued
logic is considered.
---
import PeirceLaw, IntuitionisticNot.

fix (∧) (∨) (⟺) (∃).
assume and_eq_nimp: (P ∧ Q) = (¬(P ⟹ ¬Q)).
assume or_eq_imp: (P ∨ Q) = (¬P ⟹ Q).
assume iff_eq_and: (P ⟺ Q) = ((P ⟹ Q) ∧ (Q ⟹ P)).
assume ex_eq_nall: (∃x. P.[x]) = (¬(∀x. ¬P.[x])).

begin

interpret! Std.Classical;
	interpret IntuitionisticNot.PeirceLaw.
	interpret ClassicalNot.
	interpret Std.And;
		by #simp and_eq_nimp #intro nimp_not_intro nnot_intro #elim nimp_not_elim nnot_elim.
	interpret! Eq.Iff;
		by #simp iff_eq_and.
	interpret Iff_Not: Iff.Not, Iff_Not.ClassicalNot.
	interpret Std.Or;
		by #simp or_eq_imp #elim not_elim not_imp_elim.
	interpret Std.Ex;
		- for x P if Px; simp ex_eq_nall; apply nall_intro; simp;
			- for Q if assm;
				by assm[OF Px].
			.
		- for P; simp ex_eq_nall;
			- if nall;
				apply nall_elim[OF nall];
				simp;
				- for x if Px for Q if assm;
					by assm[OF Px].
				.
			.
		.
	.

