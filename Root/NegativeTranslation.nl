------
# Gödel―Gentzen Negative Translation
------
base TypedIntuitionisticLogic;

----
The intuitionistic logic can prove theorems of the classical logic after a double-negation translation.
To formally state the result, we interpret the classical logic context, replacing the `prop` type of by the image of double negation,
disjunction and existential quantifier by certain forms.

Since we have not introduced convenient methods such as equality to specify such, we use axioms to do so.
----

fix image_nnot nnot_or nnot_ex;

-- `image_nnot` should turn a proposition into a proposition.

assume prop_image_nnot#intro: prop P ⟹ prop (image_nnot P);

--

assume image_nnot_iff_ex: prop P ⟹ image_nnot P ⟺ (∃P' : prop. P ⟺ ¬¬P');
assume image_nnot_imp_prop: image_nnot P ⟹ prop P;
assume prop_image_nnot! prop P ⟹ prop (image_nnot P);

lemma image_nnot_iff: if [prop P] then image_nnot P ⟺ (¬¬P ⟺ P) :=
	apply iff_intro;
	-  if tP: image_nnot P :=
		apply ex_elim[OF tP[unfolded image_nnot_iff_ex]];
		- for P', if iff: (P ⟺ ¬¬P'), [prop P'] :=
			unfold+ iff nnnot_iff;
			done;
		done;
	- if nn: ¬¬P ⟺ P :=
		unfold image_nnot_iff_ex;
		apply ex_intro;
		- for P', if imp: ∀x. (P ⟺ ¬¬x) ⟹ prop x ⟹ P', [prop P'] :=
			apply imp(P);
			unfold nn;
			done;
		done;
	done;

--The negative translation of disjunction is specified as follows.

assume nnot_or_iff: nnot_or P Q ⟺ ¬(¬P ∧ ¬Q);

---
In this context, it is necessary to assume that this operation is well-typed.
We should be able to derive the fact if we introduce equality and definition.
---
import nnot_or: Magma prop nnot_or;

-- The existential quantifier is translated as follows:

assume nnot_ex_iff: nnot_ex ι (x. α.[x]) ⟺ ¬(∀x:ι. ¬α.[x]);

import nnot_ex: TypedBinder prop nnot_ex;

begin
----
## Proving that the image of double negation and operators satisfy the classical logic axioms.
----

interpret image_nnot: ClassicalLogic :=
	instantiate image_nnot;
	instantiate true;
	- by #unfold image_nnot_iff not_true_iff not_false_iff;
	- done;
	instantiate false;
	- by #unfold image_nnot_iff not_true_iff not_false_iff;
	- for P Q, if tP: image_nnot P, tQ: image_nnot Q then image_nnot (P ⟹ Q) :=
		note! image_nnot_imp_prop[OF tP];
		note! image_nnot_imp_prop[OF tQ];
		have nnQ: ¬¬Q ⟺ Q :=
			by tQ[unfolded image_nnot_iff];
		unfold image_nnot_iff;
		fold nnQ;
		by #unfold nnimp_not_iff;
	instantiate (¬);
	- for P, if tP: image_nnot P then image_nnot (¬P) :=
		note! image_nnot_imp_prop[OF tP];
		by #unfold image_nnot_iff tP[unfolded image_nnot_iff] nnnot_iff;
	- for P, if P0: P ⟹ false, tP: image_nnot P then ¬P :=
		by not_intro[OF P0] image_nnot_imp_prop[OF tP];
	- for P, if nP: ¬P, P: P, tP: image_nnot P then false :=
		by not_imp_false[OF nP P] image_nnot_imp_prop[OF tP];
	instantiate (∧);
	- for P Q, if tP: image_nnot P, tQ: image_nnot Q then image_nnot (P ∧ Q) :=
		note! image_nnot_imp_prop[OF tP];
		note! image_nnot_imp_prop[OF tQ];
		unfold image_nnot_iff nnand_iff;
		by #unfold tP[unfolded image_nnot_iff] tQ[unfolded image_nnot_iff];
	- by and_intro image_nnot_imp_prop;
	- by image_nnot_imp_prop #elim and_elim;
	- by image_nnot_imp_prop #elim and_elim;
	instantiate (⟺);
	- for P Q, if tP: image_nnot P, tQ: image_nnot Q then image_nnot (P ⟺ Q) :=
		note! image_nnot_imp_prop[OF tP];
		note! image_nnot_imp_prop[OF tQ];
		unfold image_nnot_iff;
		fold tP[unfolded image_nnot_iff];
		fold tQ[unfolded image_nnot_iff];
		by #unfold nniff_iff;
	- by iff_intro image_nnot_imp_prop;
	- by image_nnot_imp_prop #elim iff_elim1;
	- by image_nnot_imp_prop #elim iff_elim2;
	instantiate nnot_or;
	- for P Q, if tP: image_nnot P, tQ: image_nnot Q then image_nnot (nnot_or P Q) :=
		note! image_nnot_imp_prop[OF tP];
		note! image_nnot_imp_prop[OF tQ];
		note! nnot_or.type;
		by #unfold image_nnot_iff nnot_or_iff nnnot_iff;
	- by image_nnot_imp_prop #unfold+ nnot_or_iff;
	- for P Q, if Q: Q then nnot_or P Q :=
		unfold+ nnot_or_iff iff_true[OF Q] not_true_iff and_false_iff;
		by not_false;
	- for P Q, if 1: nnot_or P Q, tR: image_nnot R, PR: P ⟹ R, QR: Q ⟹ R then R :=
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
				done;
			by nnR[unfolded nnRR];
		done;
	end;

interpret all: Binder image_nnot (∀) :=
	- if ta: ∀x. image_nnot α.[x] then image_nnot (∀x. α.[x]) :=
		unfold image_nnot_iff;
		apply+ and_intro all.type;
		note 1: ta[unfolded+ image_nnot_iff all_and_iff];
		note! and_elim1[OF 1];
		fold and_elim2[OF 1];
		unfold nnall_not_iff;
		unfold and_elim2[OF 1];
		by iff.refl;
	end;

interpret not: Unary image_nnot (¬) :=
	- if pP: image_nnot P then image_nnot (¬P) :=
		unfold+ image_nnot_iff nnnot_iff iff_true[OF iff.refl] and_true_iff;
		apply+ not.type image_nnot_imp_type[OF pP];
		done;
	end;

interpret ex: PropEx image_nnot nnot_ex :=
	- if ta: ∀x. image_nnot α.[x] then image_nnot (nnot_ex (x. α.[x])) :=
		unfold image_nnot_iff;
		apply+ and_intro nnot_ex.type;
		note 1: ta[unfolded+ image_nnot_iff all_and_iff];
		note! and_elim1[OF 1];
		unfold+ nnot_ex_iff nnnot_iff;
		done;
	- for x, if ax: α.[x] then nnot_ex (x'. α.[x']) :=
		unfold nnot_ex_iff;
		apply not_intro;
		- if alln: ∀x'. ¬ α.[x'] :=
			by not_imp_false[OF alln ax];
			done;
	- if nnex: nnot_ex (x. α.[x]), tP: image_nnot P, all: ∀x. α.[x] ⟹ P then P :=
		fold image_nnot_imp_iff[OF tP];
		apply not_intro;
		- if nP: ¬P :=
			apply not_imp_false[OF nnex[unfolded nnot_ex_iff]];
			show! ¬ α.[x] :=
				apply not_intro;
				case ax: α.[x] :=
					apply not_imp_false[OF nP];
					by all[OF ax];
				done;
			done;
		done;
	end;

interpret ExcludedMiddle image_nnot nnot_or (¬) :=
	- if pP: image_nnot P then nnot_or P (¬P) :=
		unfold+ nnot_or_iff nand_nnot_iff;
		unfold and_iff.commute;
		apply non_contradiction;
		done;
	end;

;

ctxt;

end;

thm image_nnot.nnot_iff;

thm image_nnot.pierces_law;

