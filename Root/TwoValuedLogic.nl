base Equal;

import TwoValued;

interpret DefineFalse;
interpret DefineNot;
interpret TwoValuedNot;
interpret DefineOr;
interpret DefineEx;
interpret UntypedLogic;

setup cong iff_cong_not iff_cong_ex;

show false_imp_eq: (false ⟹ P) = true :=
	apply eq_true;
	by false_elim;

interpret and: MetaLeftAbsorb (∧) false (=) :=
	discharge (false ∧ P) = false :=
		unfold+ and_def false_imp_eq true_imp_eq;
		fold false_def;
		done;
	end;

interpret and: MetaRightAbsorb (∧) false (=) :=
	discharge (P ∧ false) = false :=
		unfold+ and_def false_imp_eq true_imp_eq imp_true_eq;
		fold false_def;
		done;
	end;

define prop x := ∀P. (x = true ⟹ P) ⟹ (x = false ⟹ P) ⟹ P;

show prop_elim: if x: prop x, 1: x = true ⟹ P, 0: x = false ⟹ P then P :=
	by x[unfolded prop_def][OF 1 0];

show nnot_eq: if p: prop P then (¬¬P) = P :=
	apply prop_elim[OF p];
	case P1: P = true :=
		unfold+ P1 not_true_eq not_false_eq;
		done;
	case P0: P = false :=
		unfold+ P0 not_false_eq not_true_eq;
		done;
	qed;

interpret or: MetaLeftAbsorb (∨) true (=) :=
	discharge (true ∨ P) = true :=
		apply+ eq_true or_intro1;
		done;
	end;

interpret or: MetaRightAbsorb (∨) true (=) :=
	discharge (P ∨ true) = true :=
		apply+ eq_true or_intro2;
		done;
	end;

show false_or_false_eq: (false ∨ false) = false :=
	unfold+ or_def false_imp_eq true_imp_eq;
	unfold false_def;
	done;

interpret ExcludedMiddle prop (∨) (¬) :=
	discharge if p: prop P then P ∨ ¬P :=
		apply prop_elim[OF p];
		case P1: P = true :=
			unfold+ P1 or.left_absorb;
			done;
		case P0: P = false :=
			unfold+ P0 not_false_eq or.right_absorb;
			done;
		qed;
	end;

interpret true: Member prop true :=
	discharge prop true :=
		unfold+ prop_def eq_true[OF eq.refl] true_imp_eq ;
		done;
	end;

interpret false: Member prop false :=
	discharge prop false :=
		unfold+ prop_def eq_true[OF eq.refl] or.right_absorb;
		done;
	end;

interpret not: Unary prop (¬) :=
	discharge if p: prop P then prop (¬P) :=
		apply prop_elim[OF p];
		case P1: P = true :=
			unfold+ P1 not_true_eq;
			by false.type;
		case P0: P = false :=
			unfold+ P0 not_false_eq;
			by true.type;
		qed;
	end;

interpret imp: Magma prop (⟹) :=
	discharge if P: prop P, Q: prop Q then prop (P ⟹ Q) :=
		apply prop_elim[OF P];
		case P1: P = true :=
			unfold+ P1 true_imp_eq;
			by Q;
		case P0: P = false :=
			unfold+ P0 false_imp_eq;
			by true.type;
		qed;
	end;

interpret and: Magma prop (∧) :=
	discharge if P: prop P, Q: prop Q then prop (P ∧ Q) :=
		apply prop_elim[OF P];
		case P1: P = true :=
			apply prop_elim[OF Q];
			case Q1: Q = true :=
				unfold+ P1 Q1 true_and_true_eq;
				by true.type;
			case Q0: Q = false :=
				unfold+ Q0 and.right_absorb;
				by false.type;
			qed;
		case P0: P = false :=
			unfold+ P0 and.left_absorb;
			by false.type;
		qed;
	end;

interpret iff: Magma prop (⟺) :=
	discharge if p: prop P, q: prop Q then prop (P ⟺ Q) :=
		unfold iff_def;
		apply+ and.type imp.type p q;
		qed;
	end;

show true_iff_false_eq: (true ⟺ false) = false :=
	unfold+ iff_def true_imp_eq and.left_absorb;
	done;

show false_iff_true_eq: (false ⟺ true) = false :=
	unfold+ iff_def true_imp_eq and.right_absorb;
	done;

interpret or: Magma prop (∨) :=
	discharge if p: prop P, q: prop Q then prop (P ∨ Q) :=
		apply prop_elim[OF p];
		case P1: P = true :=
			unfold+ P1 or.left_absorb;
			by true.type;
		case P0: P = false :=
			apply prop_elim[OF q];
			case Q1: Q = true :=
				unfold+ Q1 or.right_absorb;
				by true.type;
			case Q0: Q = false :=
				unfold+ P0 Q0 false_or_false_eq;
				by false.type;
			qed;
		qed;
	end;

show all_true_eq: (∀x. true) = true :=
	apply eq_true;
	by true_intro;

show ex_false_eq: (∃x. false) = false :=
	unfold+ ex_def false_imp_eq all_true_eq true_imp_eq;
	unfold false_def;
	done;

interpret PropOr prop (∨) :=
	know;
	know;
	know;
	discharge if or: P ∨ Q, R: prop R, PR: P ⟹ R, QR: Q ⟹ R then R :=
		by or_elim[OF or PR QR];
	end;

show not_prop_iff: ¬ prop x ⟺ x ≠ true ∧ x ≠ false :=
	unfold+ prop_def neq_def;
	unfold(⟺) nor_iff;
	done;

show not_prop_elim: if np: ¬ prop P then (P ≠ true ⟹ P ≠ false ⟹ Q) ⟹ Q :=
	by and_elim[OF np[unfolded(⟺) not_prop_iff]];
