base Lambda;

import TwoValued;


show eq_true: if P: P then P = true;
	by imp_imp_eq[OF P true_intro];

show true_eq: if P: P then true = P;
	unfold eq_true[OF P];
	done;

show eq_refl_eq_true: (x = x) = true;
	by eq_true[OF eq.refl];

show weaken_eq: (P ⟹ Q ⟹ P) = true;
	by eq_true[OF weaken];

show eq_true_iff: P = true ⟺ P;
	apply iff_intro;
	case Pt: P = true;
		unfold Pt;
		done;
	by eq_true;

show true_eq_iff: true = P ⟺ P;
	unfold[iff] eq_iff.commute;
	by eq_true_iff;

show imp_true_eq: (P ⟹ true) = true;
	by eq_true[OF weaken[OF true_intro]];

show true_and_true_eq: (true ∧ true) = true;
	by eq_true[OF true_and_true];

---
Moreover, we assume that the following identity.
---
show true_imp_eq: (true ⟹ P) = P;
	by imp_eq[OF true_intro];

locale TwoValuedNot :=
	fix false;
	interpret DefineNot;
	show not_false_eq: (¬false) = true;
		apply eq_true;
		by not_false;

	show not_true_eq: (¬true) = false;
		unfold not_def;
		by true_imp_eq;
	end;

locale TwoValuedUntypedLogic :=
	import DefineFalse;
	import TwoValuedNot;

	show false_imp_eq: (false ⟹ P) = true;
		apply eq_true;
		by false_imp;

	show and_false_eq: (P ∧ false) = false;
		unfold* and_def false_imp_eq imp_true_eq true_imp_eq;
		fold false_def;
		done;

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
	fix false;
	interpret TwoValuedNot false;
	interpret DefineOr;
	interpret DefineEx;
	interpret UntypedMinimalLogic;

	define prop P := (P = true ∨ P = false);

	note prop_elim: if P: prop P then or_elim[OF P[unfolded prop_def]];

	show not_prop_iff: ¬ prop x ⟺ x ≠ true ∧ x ≠ false;
		unfold+ prop_def neq_def;
		unfold[iff] nor_iff;
		done;

	interpret true: Member prop true :=
		discharge prop true;
			unfold prop_def;
			unfold[iff]+ iff_true[OF eq.refl] true_imp_iff iff_true[OF true_or] iff_true_iff;
			done;
		end;

	interpret false: Member prop false :=
		discharge prop false;
			unfold prop_def;
			unfold[iff]* iff_true[OF eq.refl] iff_true[OF or_true] iff_true_iff;
			done;
		end;

	interpret not: Unary prop (¬) :=
		discharge if p: prop P then prop (¬P);
			apply prop_elim[OF p];
			case P1: P = true;
				unfold* P1 not_true_eq;
				by false.type;
			case P0: P = false;
				unfold* P0 not_false_eq;
				by true.type;
			qed;
		end;

	interpret imp: Magma prop (⟹) :=
		discharge if P: prop P, Q: prop Q then prop (P ⟹ Q);
			apply prop_elim[OF P];
			case P1: P = true;
				unfold* P1 true_imp_eq;
				by Q;
			case P0: P = false;
				unfold* P0 false_imp_eq;
				by true.type;
			qed;
		end;

	interpret and: Magma prop (∧) :=
		discharge if P: prop P, Q: prop Q then prop (P ∧ Q);
			apply prop_elim[OF P];
			case P1: P = true;
				apply prop_elim[OF Q];
				case Q1: Q = true;
					unfold* P1 Q1 true_and_true_eq;
					by true.type;
				case Q0: Q = false;
					unfold* Q0 and_false_eq;
					by false.type;
				qed;
			case P0: P = false;
				unfold* P0 false_and_eq;
				by false.type;
			qed;
		end;

	interpret iff: Magma prop (⟺) :=
		discharge if p: prop P, q: prop Q then prop (P ⟺ Q);
			unfold iff_def;
			apply+ and.type imp.type p q;
			qed;
		end;

}

show true_or_eq: (true ∨ P) = true;
	by eq_true[OF true_or];

show or_true_eq: (P ∨ true) = true;
	by eq_true[OF or_true];

show false_or_false_eq: (false ∨ false) = false;
	unfold+ or_def false_imp_eq true_imp_eq;
	unfold false_def;
	done;

ctxt;

