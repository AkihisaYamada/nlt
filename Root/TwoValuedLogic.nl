base Lambda;

import TwoValuedLambda;


locale TwoValuedUntypedLogic :=
	fix false;
	interpret TwoValuedNot;
	interpret DefineOr;

	define prop P := (P = true ∨ P = false);

	note prop_elim: if P: prop P then or_elim[OF P[unfolded prop_def]];

	show false_imp: if p: prop P, f: false then P;
		apply prop_elim[OF p];
		case P1: P = true;
			unfold P1;
			done;
		case P0: P = false;
			unfold P0;
			by f;
		qed;

	show false_imp_eq: if p: prop P then (false ⟹ P) = true;
		apply eq_true;
		by false_imp[OF p];

	show true_or_true: (true ∨ P) = true;
		apply+ eq_true or_intro1;
		done;

	show or_true_eq: (P ∨ true) = true;
		apply+ eq_true or_intro2;
		done;

	show and_false_eq: if p: prop P then (P ∧ false) = false;
		apply prop_elim[OF p];
		case P1: P = true;
			unfold+ P1 and_def true_imp_eq;
oops

	show false_and_eq: (false ∧ P) = false;
		unfold* and_def false_imp_eq true_imp_eq;
		fold false_def;
		done;

	show true_iff_false_eq: (true ⟺ false) = false;
		unfold* iff_def true_imp_eq false_and_eq;
		done;

	show false_iff_true_eq: (false ⟺ true) = false;
		unfold* iff_def true_imp_eq and_false_eq;
		done;

	end;

----
## Propositions as True or False

By saying propositions are either true or false, one can type finitary operations.
----

locale LambdaIntuitionisticLogic :=

}

ctxt;

