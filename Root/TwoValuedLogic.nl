base LambdaLogic;

import TwoValued;

finalize;

interpret TwoValuedTrue;

show true_and_true_eq: (true ∧ true) = true :=
	by eq_true[OF true_and_true];

show eq_true_iff: P = true ⟺ P :=
	apply iff_intro;
	- if Pt: P = true :=
		unfold Pt;
		done;
	by eq_true;

show true_eq_iff: true = P ⟺ P :=
	unfold(⟺) eq_iff.commute;
	by eq_true_iff;

show false_imp_eq: (false ⟹ P) = true :=
	apply eq_true;
	by false_elim;

show not_false_eq: (¬false) = true :=
	apply eq_true;
	by not_false;

show not_true_eq: (¬true) = false :=
	unfold not_def;
	by true_imp_eq;

interpret and: MetaLeftAbsorb (∧) false (=) :=
	- (false ∧ P) = false :=
		unfold+ and_def false_imp_eq true_imp_eq;
		fold false_def;
		done;
	done;

interpret and: MetaRightAbsorb (∧) false (=) :=
	- (P ∧ false) = false :=
		unfold+ and_def false_imp_eq true_imp_eq imp_true_eq;
		fold false_def;
		done;
	done;

interpret or: MetaLeftAbsorb (∨) true (=) :=
	- (true ∨ P) = true :=
		apply+ eq_true or_intro1;
		done;
	done;

interpret or: MetaRightAbsorb (∨) true (=) :=
	- (P ∨ true) = true :=
		apply+ eq_true or_intro2;
		done;
	done;

show false_or_false_eq: (false ∨ false) = false :=
	unfold+ or_def false_imp_eq true_imp_eq;
	unfold false_def;
	done;

show true_iff_false_eq: (true ⟺ false) = false :=
	unfold+ iff_def true_imp_eq and.left_absorb;
	done;

show false_iff_true_eq: (false ⟺ true) = false :=
	unfold+ iff_def true_imp_eq and.right_absorb;
	done;

show all_true_eq: (∀x. true) = true :=
	apply eq_true;
	by true_intro;

show ex_false_eq: (∃x. false) = false :=
	unfold+ ex_def false_imp_eq all_true_eq true_imp_eq;
	unfold false_def;
	done;

define prop x := x = true ∨ x = false;

show prop_elim: if x: prop x, 1: x = true ⟹ P, 0: x = false ⟹ P then P :=
	apply or_elim[OF x[unfolded prop_def]];
	just 1 0;

show nnot_eq: if p: prop P then (¬¬P) = P :=
	apply prop_elim[OF p];
	- if P1: P = true :=
		unfold+ P1 not_true_eq not_false_eq;
		done;
	- if P0: P = false :=
		unfold+ P0 not_false_eq not_true_eq;
		done;
	done;

interpret ClassicalLogic :=
	- prop (prop x) :=
		unfold prop_def;
		apply or_intro;
		- for R, if 1: prop x = true ⟹ R, 2: prop x = false ⟹ R :=
			

	- if p: prop P then P ∨ ¬P :=
		apply prop_elim[OF p];
		- if P1: P = true :=
			unfold+ P1 or.left_absorb;
			done;
		- if P0: P = false :=
			unfold+ P0 not_false_eq or.right_absorb;
			done;
		done;
	done;

interpret true: Member prop true :=
	- prop true :=
		unfold+ prop_def eq_true[OF eq.refl] true_imp_eq or.left_absorb;
		done;
	done;

interpret false: Member prop false :=
	- prop false :=
		unfold+ prop_def eq_true[OF eq.refl] or.right_absorb;
		done;
	done;

interpret not: Unary prop (¬) :=
	- if p: prop P then prop (¬P) :=
		apply prop_elim[OF p];
		- if P1: P = true :=
			unfold+ P1 not_true_eq;
			by false.type;
		- if P0: P = false :=
			unfold+ P0 not_false_eq;
			by true.type;
		done;
	done;

interpret imp: Magma prop (⟹) :=
	- if P: prop P, Q: prop Q then prop (P ⟹ Q) :=
		apply prop_elim[OF P];
		- if P1: P = true :=
			unfold+ P1 true_imp_eq;
			by Q;
		- if P0: P = false :=
			unfold+ P0 false_imp_eq;
			by true.type;
		done;
	done;

interpret and: Magma prop (∧) :=
	- if P: prop P, Q: prop Q then prop (P ∧ Q) :=
		apply prop_elim[OF P];
		- if P1: P = true :=
			apply prop_elim[OF Q];
			- if Q1: Q = true :=
				unfold+ P1 Q1 true_and_true_eq;
				by true.type;
			- if Q0: Q = false :=
				unfold+ Q0 and.right_absorb;
				by false.type;
			qed;
		- if P0: P = false :=
			unfold+ P0 and.left_absorb;
			by false.type;
		done;
	done;

interpret iff: Magma prop (⟺) :=
	- if p: prop P, q: prop Q then prop (P ⟺ Q) :=
		unfold iff_def;
		apply+ and.type imp.type p q;
		done;
	done;

interpret or: Magma prop (∨) :=
	- if p: prop P, q: prop Q then prop (P ∨ Q) :=
		apply prop_elim[OF p];
		- if P1: P = true :=
			unfold+ P1 or.left_absorb;
			by true.type;
		- if P0: P = false :=
			apply prop_elim[OF q];
			- if Q1: Q = true :=
				unfold+ Q1 or.right_absorb;
				by true.type;
			- if Q0: Q = false :=
				unfold+ P0 Q0 false_or_false_eq;
				by false.type;
			done;
		done;
	done;

interpret PropOr prop (∨) :=
	know;
	know;
	know;
	- if or: P ∨ Q, R: prop R, PR: P ⟹ R, QR: Q ⟹ R then R :=
		by or_elim[OF or PR QR];
	done;

show not_prop_iff: ¬ prop x ⟺ x ≠ true ∧ x ≠ false :=
	unfold+ prop_def neq_def;
	unfold(⟺) nor_iff;
	done;

show not_prop_elim: if np: ¬ prop P then (P ≠ true ⟹ P ≠ false ⟹ Q) ⟹ Q :=
	by and_elim[OF np[unfolded(⟺) not_prop_iff]];
