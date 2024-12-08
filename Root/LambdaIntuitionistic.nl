base TwoValuedLogic;

---
## Intuitionistic Types
---

define iprop x := ¬¬ prop x;

show iprop_intro: if 1: P ≠ true ⟹ P ≠ false ⟹ false then iprop P;
	unfold iprop_def;
	apply not_intro;
	case n: ¬ prop P;
		apply not_prop_elim[OF n];
		case Pn1: P ≠ true, Pn0: P ≠ false;
			by 1[OF Pn1 Pn0];
		qed;
	qed;

show iprop_elim: if nnp: iprop P, Pn1: P = true ⟹ false, Pn0: P = false ⟹ false then Q;
	show np: ¬ prop P;
		unfold[iff] not_prop_iff;
		apply and_intro;
		show! P ≠ true;
			by neq_intro[OF Pn1];
		show! P ≠ false;
			by neq_intro[OF Pn0];
		qed;
	by not_elim[OF nnp[unfolded iprop_def] np];

interpret true: Member iprop true :=
	discharge iprop true;
		unfold iprop_def;
		apply nnot_intro;
		by true.type;
	end;

interpret false: Member iprop false :=
	discharge iprop false;
		unfold iprop_def;
		apply nnot_intro;
		by false.type;
	end;

interpret not: Unary iprop (¬) :=
	discharge if p: iprop P then iprop (¬P);
		apply iprop_intro;
		case nt: (¬P) ≠ true, nf: (¬P) ≠ false;
			apply iprop_elim[OF p];
			case P1: P = true;
				show neq: false ≠ false;
					by nf[unfolded+ P1 not_true_eq];
				by neq_refl_imp_false[OF neq];
			case P0: P = false;
				show neq: true ≠ true;
					by nt[unfolded+ P0 not_false_eq];
				by neq_refl_imp_false[OF neq];
			qed;
		qed;
	end;

interpret imp: Magma iprop (⟹) :=
	discharge if nnp: iprop P, nnq: iprop Q then iprop (P ⟹ Q);
		apply iprop_intro;
		case nt: (P ⟹ Q) ≠ true, nf: (P ⟹ Q) ≠ false;
			apply iprop_elim[OF nnp];
			case P1: P = true;
				apply iprop_elim[OF nnq];
				case Q1: Q = true;
					show tnt: true ≠ true;
						by nt[unfolded+ Q1 imp.right_absorb];
					by neq_refl_imp_false[OF tnt];
				case Q0: Q = false;
					show fnf: false ≠ false;
						by nf[unfolded+ P1 Q0 imp.left_neutral];
					by neq_refl_imp_false[OF fnf];
				qed;
			case P0: P = false;
				show neq: true ≠ true;
					by nt[unfolded+ P0 false_imp_eq];
				by neq_refl_imp_false[OF neq];
			qed;
		qed;
	end;

interpret and: Magma iprop (∧) :=
	discharge if nnp: iprop P, nnq: iprop Q then iprop (P ∧ Q);
		apply iprop_intro;
		case nt: (P ∧ Q) ≠ true, nf: (P ∧ Q) ≠ false;
			apply iprop_elim[OF nnp];
			case P1: P = true;
				apply iprop_elim[OF nnq];
				case Q1: Q = true;
					show tnt: true ≠ true;
						by nt[unfolded+ P1 Q1 true_and_true_eq];
					by neq_refl_imp_false[OF tnt];
				case Q0: Q = false;
					show fnf: false ≠ false;
						by nf[unfolded+ Q0 and.right_absorb];
					by neq_refl_imp_false[OF fnf];
				qed;
			case P0: P = false;
				show fnf: false ≠ false;
					by nf[unfolded+ P0 and.left_absorb];
				by neq_refl_imp_false[OF fnf];
			qed;
		qed;
	end;

interpret iff: Magma iprop (⟺) :=
	discharge if p: iprop P, q: iprop Q then iprop (P ⟺ Q);
		unfold iff_def;
		apply+ and.type imp.type p q;
		qed;
	end;

interpret or: Magma iprop (∨) :=
	discharge if nnp: iprop P, nnq: iprop Q then iprop (P ∨ Q);
		apply iprop_intro;
		case nt: (P ∨ Q) ≠ true, nf: (P ∨ Q) ≠ false;
			apply iprop_elim[OF nnp];
			case P1: P = true;
				show tnt: true ≠ true;
					by nt[unfolded+ P1 or.left_absorb];
				by neq_imp_false[OF tnt eq.refl];
			case P0: P = false;
				apply iprop_elim[OF nnq];
				case Q1: Q = true;
					show tnt: true ≠ true;
						by nt[unfolded+ Q1 or.right_absorb];
					by neq_imp_false[OF tnt eq.refl];
				case Q0: Q = false;
					show fnf: false ≠ false;
						by nf[unfolded+ P0 Q0 false_or_false_eq];
					by neq_imp_false[OF fnf eq.refl];
				qed;
			qed;
		qed;
	end;

import all: Binder iprop (∀);

import ex: Binder iprop (∃);

interpret PropEx iprop (∃) :=
	know;
	know;
	discharge if ex: ∃x. α.[x], P: iprop P, all: ∀x. α.[x] ⟹ P then P;
		by ex_elim[OF ex all];
	end;

interpret TypedIntuitionisticLogic iprop;


ctxt;


