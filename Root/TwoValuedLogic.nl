base LambdaLogic;

import TwoValued;

finalize;

interpret TwoValuedTrue;

lemma true_and_true_eq: (true ∧ true) = true :=
	by eq_true[OF true_and_true];

lemma eq_true_iff: P = true ⟺ P :=
	apply iff_intro;
	- if Pt: P = true :=
		unfold Pt;
		done;
	by eq_true;

lemma true_eq_iff: true = P ⟺ P :=
	unfold(⟺) eq_iff.commute;
	by eq_true_iff;

lemma false_imp_eq: (false ⟹ P) = true :=
	apply eq_true;
	by false_elim;

lemma not_false_eq: (¬false) = true :=
	apply eq_true;
	by not_false;

lemma not_true_eq: (¬true) = false :=
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

lemma false_or_false_eq: (false ∨ false) = false :=
	unfold+ or_def false_imp_eq true_imp_eq;
	unfold false_def;
	done;

lemma true_iff_false_eq: (true ⟺ false) = false :=
	unfold+ iff_def true_imp_eq and.left_absorb;
	done;

lemma false_iff_true_eq: (false ⟺ true) = false :=
	unfold+ iff_def true_imp_eq and.right_absorb;
	done;

lemma all_true_eq: (∀x. true) = true :=
	apply eq_true;
	by true_intro;

lemma ex_false_eq: (∃x. false) = false :=
	unfold+ ex_def false_imp_eq all_true_eq true_imp_eq;
	unfold false_def;
	done;

define prop x := x = true ∨ x = false;

lemma prop_elim: if x: prop x, 1: x = true ⟹ P, 0: x = false ⟹ P then P :=
	apply or_elim[OF x[unfolded prop_def]];
	just 1 0;

lemma nnot_eq: if p: prop P then (¬¬P) = P :=
	apply prop_elim[OF p];
	- if P1: P = true :=
		unfold+ P1 not_true_eq not_false_eq;
		done;
	- if P0: P = false :=
		unfold+ P0 not_false_eq not_true_eq;
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
			done;
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

interpret typed: PropositionalClassical :=
	- if P0: P ⟹ false, [prop P] then ¬ P :=
		by not_intro[OF P0];
	- if nP: ¬P, [P, prop P] then false :=
		by not_imp_false[OF nP];
	- P ⟹ Q ⟹ prop P ⟹ prop Q ⟹ P ∧ Q :=
		by and_intro;
	- if PQ: P ∧ Q then prop P ⟹ prop Q ⟹ P :=
		by and_elim1[OF PQ];
	- if PQ: P ∧ Q then prop P ⟹ prop Q ⟹ Q :=
		by and_elim2[OF PQ];
	- if PQ: P ⟹ Q, QP: Q ⟹ P then prop P ⟹ prop Q ⟹ P ⟺ Q :=
		by iff_intro[OF PQ QP];
	- if PQ: P ⟺ Q then P ⟹ prop P ⟹ prop Q ⟹ Q :=
		by iff_elim1[OF PQ];
	- if PQ: P ⟺ Q then Q ⟹ prop P ⟹ prop Q ⟹ P :=
		by iff_elim2[OF PQ];
	- P ⟹ prop P ⟹ prop Q ⟹ P ∨ Q :=
		by or_intro1;
	- Q ⟹ prop P ⟹ prop Q ⟹ P ∨ Q :=
		by or_intro2;
	- if PQ: P ∨ Q, PR: P ⟹ R, QR: Q ⟹ R then prop P ⟹ prop Q ⟹ prop R ⟹ R :=
		by or_elim[OF PQ PR QR];
	- if f: false then prop P ⟹ P :=
		by false_elim[OF f];
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

thm typed.pierces_law;

lemma not_prop_iff: ¬ prop x ⟺ x ≠ true ∧ x ≠ false :=
	unfold+ prop_def neq_def;
	unfold(⟺) nor_iff;
	done;

lemma not_prop_elim: if np: ¬ prop P, imp: P ≠ true ⟹ P ≠ false ⟹ Q then Q :=
	apply and_elim[OF np[unfolded(⟺) not_prop_iff]];
	just imp;

ctxt;
