import True, Or.
fix false.
assume false_prop: false : Prop.
assume true_or_false: if P : Prop then P = true ∨ P = false.

lemma true_or_false_cases:
	if 1: P = true ⟹ Q, 0: P = false ⟹ Q, P! P : Prop, [Q : Prop] then Q;
	apply true_or_false[OF P, THEN or_elim];
	- by 1.
	- by 0.
	by false_prop.

instance False;
	- if 0: false, [P : Prop] then P;
		apply true_or_false_cases[of P];
		- if P1: P = true; unfold P1.
		- if P0: P = false; unfold P0; apply 0.
		.
	.

import Imp, And, Or, Not, IntuitionisticNot.


begin

note Prop_elim_cases: true_or_false_cases[OF > > _].

lemma eq_true! if P: P, [P : Prop] then P = true;
	apply true_or_false_cases[of P];
	- if P0: P = false;
		apply false_elim[OF P[unfold P0]].
	.

note true_eq! eq_true[THEN eq.sym].

lemma not_false_eq_true#simp (¬false) = true; by not_false.

lemma not_true_eq_false#simp (¬true) = false;
	note! eq_prop[of Prop].
	apply true_or_false_cases[of (¬true)];
	- if n: (¬true) = true;
		by not_imp_false[of true] #simp n.
	.

lemma not_imp_eq_false#simp[after 1] if nP: ¬P, [P : Prop] then P = false;
	apply true_or_false_cases[of P];
	- if P1: P = true;
		apply false_elim[OF nP[simp P1]];.
	.
note not_imp_false_eq: not_imp_eq_false[THEN eq.sym].

instance[no_rewrite] .Classical;
	interpret ClassicalNot;
		- if nnP: ¬ ¬ P, [P : Prop] then P;
			apply true_or_false_cases[of P];
			- if P1: P = true; unfold P1.
			- if P0: P = false; use nnP[simp P0]; by #elim false_elim.
			.
		.
	interpret[no_rewrite] Iff;
		instantiate (⟷) := (=).
		- if PQ: P ⟹ Q, QP: Q ⟹ P, ... then P = Q;
			apply true_or_false_cases[of P];
			- if P1: P = true; by PQ #simp P1.
			- if P0: P = false;
				unfold P0;
				by not_imp_false_eq not_intro #elim QP[unfold P0].
			.
		- if PQ: P = Q, ...; fold PQ.
		- if PQ: P = Q, ...; unfold PQ.
		.
	instantiate (⟷) := (=).
	.

instance IMP: Antisymmetric Prop (⟶);
	- if PQ: P ⟶ Q, QP: Q ⟶ P, ... then P = Q;
		apply true_or_false_cases[of P];
		- if P1: P = true; by PQ[THEN imp_elim1] #simp P1.
		- if P0: P = false; apply true_or_false_cases[of Q];
			- if Q1: Q = true;
				have 0: false; fold P0; by QP[THEN imp_elim1] #simp Q1.
				apply false_elim[OF 0].
			- if Q0: Q = false; unfold P0 Q0.
			.
		.
	.
