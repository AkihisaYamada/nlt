------
# Gödel―Gentzen Negative Translation

Theorems in the classical logic can be translated in a double-negated form in the intuitionistic logic.
To do so, we must replace the prop type of classical logic by the image of double negation,
disjunction and existential quantifier by certain form.
Since we have not introduced convenient methods such as equality to specify such, we use axioms to do so.
------
base TypedIntuitionisticLogic;

fix image_nnot nnot_or nnot_ex;

assume image_nnot_iff_and: image_nnot P ⟺ prop P ∧ (∃P'. prop P' ∧ (P ⟺ ¬¬P'));

show image_nnot_imp_iff: if pP: image_nnot P then ¬¬P ⟺ P :=
	note 1: pP[unfolded image_nnot_iff_and];
	apply and_elim[OF 1];
	case pP: prop P, ex: ∃P'. prop P' ∧ (P ⟺ ¬¬P') :=
		apply ex_elim[OF ex];
		apply+ iff.type not.type pP;
		unfold and_imp_iff;
		case for P', pP': prop P', P: P ⟺ ¬¬P' :=
			unfold+ P nnnot_iff;
			by iff.refl;
		qed;
	qed;

show image_nnot_imp_type: if pP: image_nnot P then prop P :=
	by and_elim1[OF pP[unfolded image_nnot_iff_and]];

show image_nnot_iff: image_nnot P ⟺ prop P ∧ (¬¬P ⟺ P) :=
	apply iff_intro;
	case pP: image_nnot P :=
		apply and_intro;
		show! prop P :=
			by and_elim1[OF pP[unfolded image_nnot_iff_and]];
		by image_nnot_imp_iff[OF pP];
	unfold+ and_imp_iff image_nnot_iff_and;
	case pP: prop P, nn: ¬¬P ⟺ P :=
		apply+ and_intro pP ex_intro1(P);
		unfold nn;
		done;
	qed;

--The negative translation of disjunction is specified as follows.

assume nnot_or_iff: nnot_or P Q ⟺ ¬(¬P ∧ ¬Q);

---
In this context, it is necessary to assume that this operation is well-typed.
We should be able to derive the fact if we introduce equality and definition.
---
import nnot_or: Magma prop nnot_or;

-- The existential quantifier is translated as follows:

assume nnot_ex_iff: nnot_ex (x. α.[x]) ⟺ ¬(∀x. ¬α.[x]);

import nnot_ex: Binder prop nnot_ex;

----
## Proving that the image of double negation and operators satisfy the classical logic axioms.
----

interpret image_nnot.true: Member image_nnot true :=
	discharge image_nnot true :=
		unfold+ image_nnot_iff not_true_iff not_false_iff iff_true[OF true.type] true_and_iff;
		by iff.refl;
	end;

interpret image_nnot.false: Member image_nnot false :=
	discharge image_nnot false :=
		unfold+ image_nnot_iff not_true_iff not_false_iff iff_true[OF false.type] true_and_iff;
		by iff.refl;
	end;

interpret image_nnot.imp: Magma image_nnot (⟹) :=
	discharge if tP: image_nnot P, tQ: image_nnot Q then image_nnot (P ⟹ Q) :=
		apply and_elim[OF tP[unfolded image_nnot_iff]];
		case pP: prop P, nnP: ¬¬P ⟺ P :=
			apply and_elim[OF tQ[unfolded image_nnot_iff]];
			case pQ: prop Q, nnQ: ¬¬Q ⟺ Q :=
				unfold image_nnot_iff;
				fold nnQ;
				unfold+ nnimp_not_iff nnQ iff_true[OF iff.refl] and_true_iff;
				apply+ prop_imp_intro pP pQ;
				qed;
			qed;
		qed;
	end;

interpret image_nnot.and: Magma image_nnot (∧) :=
	discharge if tP: image_nnot P, tQ: image_nnot Q then image_nnot (P ∧ Q) :=
		apply and_elim[OF tQ[unfolded image_nnot_iff]];
		apply and_elim[OF tP[unfolded image_nnot_iff]];
		case pP: prop P, nnP: ¬¬P ⟺ P, pQ: prop Q, nnQ: ¬¬Q ⟺ Q :=
			unfold+ image_nnot_iff nnand_iff nnP nnQ iff_true[OF iff.refl] and_true_iff;
			apply+ and.type pP pQ;
			qed;
		qed;
	end;

interpret image_nnot.iff: Magma image_nnot (⟺) :=
	discharge if tP: image_nnot P, tQ: image_nnot Q then image_nnot (P ⟺ Q) :=
		unfold image_nnot_iff;
		apply and_intro;
		show! prop (P ⟺ Q) :=
			apply+ iff.type image_nnot_imp_type[OF tP] image_nnot_imp_type[OF tQ];
			qed;
		show! ¬¬(P ⟺ Q) ⟺ (P ⟺ Q) :=
			note nnPP: image_nnot_imp_iff[OF tP];
			note nnQQ: image_nnot_imp_iff[OF tQ];
			unfold[0] iff_iff_and;
			unfold nnand_iff;
			fold[0 1] nnPP;
			fold nnQQ;
			unfold+ nnimp_not_iff nnPP nnQQ;
			fold iff_iff_and;
			done;
		qed;
	end;

interpret image_nnot.or: PropOr image_nnot nnot_or :=
	discharge if tP: image_nnot P, tQ: image_nnot Q then image_nnot (nnot_or P Q) :=
		apply and_elim[OF tQ[unfolded image_nnot_iff]];
		apply and_elim[OF tP[unfolded image_nnot_iff]];
		case pP: prop P, nnP: ¬¬P ⟺ P, pQ: prop Q, nnQ: ¬¬Q ⟺ Q :=
			unfold+ image_nnot_iff nnot_or_iff nnnot_iff iff_true[OF iff.refl] and_true_iff;
			apply+ nnot_or.type pP pQ;
			qed;
		qed;
	discharge if P: P then nnot_or P Q :=
		unfold+ nnot_or_iff iff_true[OF P] not_true_iff false_and_iff;
		by not_false;
	discharge if Q: Q then nnot_or P Q :=
		unfold+ nnot_or_iff iff_true[OF Q] not_true_iff and_false_iff;
		by not_false;
	discharge if 1: nnot_or P Q, tR: image_nnot R, PR: P ⟹ R, QR: Q ⟹ R then R :=
		apply and_elim[OF tR[unfolded image_nnot_iff]];
		case pR: prop R, nnRR: ¬¬R ⟺ R :=
			show 2: ¬(¬P ∧ ¬Q);
				by 1[unfolded nnot_or_iff];
			show nnR: ¬¬R;
				apply not_intro;
				case nR: ¬R :=
					apply not_elim[OF 2];
					apply and_intro;
					by imp_not_imp[OF PR nR] imp_not_imp[OF QR nR];
				qed;
			by nnR[unfolded nnRR];
		qed;
	end;

interpret image_nnot.all: Binder image_nnot (∀) :=
	discharge if ta: ∀x. image_nnot α.[x] then image_nnot (∀x. α.[x]) :=
		unfold image_nnot_iff;
		apply+ and_intro all.type;
		note 1: ta[unfolded+ image_nnot_iff all_and_iff];
		note! and_elim1[OF 1];
		fold and_elim2[OF 1];
		unfold nnall_not_iff;
		unfold and_elim2[OF 1];
		by iff.refl;
	end;

interpret image_nnot.not: Unary image_nnot (¬) :=
	discharge if pP: image_nnot P then image_nnot (¬P) :=
		unfold+ image_nnot_iff nnnot_iff iff_true[OF iff.refl] and_true_iff;
		apply+ not.type image_nnot_imp_type[OF pP];
		qed;
	end;

interpret image_nnot.ex: PropEx image_nnot nnot_ex :=
	discharge if ta: ∀x. image_nnot α.[x] then image_nnot (nnot_ex (x. α.[x])) :=
		unfold image_nnot_iff;
		apply+ and_intro nnot_ex.type;
		note 1: ta[unfolded+ image_nnot_iff all_and_iff];
		note! and_elim1[OF 1];
		unfold+ nnot_ex_iff nnnot_iff;
		done;
	discharge for x, if ax: α.[x] then nnot_ex (x'. α.[x']) :=
		unfold nnot_ex_iff;
		apply not_intro;
		case alln: ∀x'. ¬ α.[x'];
			by not_imp_false[OF alln ax];
		qed;
	discharge if nnex: nnot_ex (x. α.[x]), tP: image_nnot P, all: ∀x. α.[x] ⟹ P then P :=
		fold image_nnot_imp_iff[OF tP];
		apply not_intro;
		case nP: ¬P;
			apply not_imp_false[OF nnex[unfolded nnot_ex_iff]];
			show! ¬ α.[x] :=
				apply not_intro;
				case ax: α.[x] :=
					apply not_imp_false[OF nP];
					by all[OF ax];
				qed;
			qed;
		qed;
	end;

interpret image_nnot: ExcludedMiddle image_nnot nnot_or (¬) :=
	discharge if pP: image_nnot P then nnot_or P (¬P) :=
		unfold+ nnot_or_iff nand_nnot_iff;
		unfold and_iff.commute;
		apply non_contradiction;
		qed;
	end;

interpret image_nnot: ClassicalLogic image_nnot (∧) nnot_or (⟺) (¬) nnot_ex;

ctxt;

thm image_nnot.nnot_iff;

thm image_nnot.pierces_law;

