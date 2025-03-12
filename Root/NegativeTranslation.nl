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

assume prop_image_nnot! prop P ⟹ prop (image_nnot P);

--

assume image_nnot_iff_ex: prop P ⟹ image_nnot P ⟺ (∃P' : prop. P ⟺ ¬¬P');
assume image_nnot_imp_prop: image_nnot P ⟹ prop P;
assume prop_image_nnot! prop P ⟹ prop (image_nnot P);

ctxt TypedIntuitionisticLogic;

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

note! nnot_or.type;
note! nnot_ex.type;
----
## Proving that the image of double negation and operators satisfy the classical logic axioms.
----

interpret image_nnot: ClassicalLogic :=
	note? image_nnot_imp_prop;
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
		unfold+ image_nnot_iff nnand_iff;
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
	- for P Q, if tP! image_nnot P, tQ! image_nnot Q then image_nnot (nnot_or P Q) :=
		by #unfold image_nnot_iff nnot_or_iff nnnot_iff;
	- for P Q, if P: P :=
		by #unfold+ nnot_or_iff iff_true[OF P] not_true_iff false_and_iff not_false_iff;
	- for P Q, if Q: Q :=
		by #unfold+ nnot_or_iff iff_true[OF Q] not_true_iff and_false_iff not_false_iff;
	- for P Q, if 1: nnot_or P Q :=
		- for R, if PR: P ⟹ R, QR: Q ⟹ R,
			tP! image_nnot P, tQ! image_nnot Q, tR! image_nnot R then R
		:= fold tR[unfolded image_nnot_iff];
			apply not_intro;
			- if nR: ¬R :=
				have 2: ¬(¬P ∧ ¬Q) :=
					by 1[unfolded nnot_or_iff];
				apply not_elim[OF 2];
				apply and_intro;
				by imp_not_imp[OF PR nR] imp_not_imp[OF QR nR];
			done;
		done;
	instantiate (∀:);
	- for ι α, if ta! ∀x. ι x ⟹ image_nnot α.[x] then image_nnot (∀x:ι. α.[x]) :=
		unfold image_nnot_iff;
		have nna: for x, if xt! ι x then α.[x] ⟺ (¬¬α.[x]) :=
			by #unfold ta[OF xt][unfolded image_nnot_iff];
		unfold nna;
		by #unfold nnall_not_iff;
	- by all_intro #force;
	- for x ι α, if all: ∀y:ι. α.[y], [∀y. ι y ⟹ image_nnot α.[y], ι x] then α.[x] :=
		apply all_elim[OF all];
		done;
	instantiate nnot_ex;
	- for ι α, if ta! ∀x. ι x ⟹ image_nnot α.[x] then image_nnot (nnot_ex ι (x. α.[x])) :=
		unfold image_nnot_iff;
		by #unfold nnot_ex_iff nnnot_iff;
	- for x α ι, if [α.[x], ι x], ta! ∀y. ι y ⟹ image_nnot α.[y] then nnot_ex ι (z. α.[z]) :=
		unfold nnot_ex_iff;
		apply not_intro;
		- if an: ∀y:ι. ¬α.[y] :=
			apply all_elim[OF an];
			by not_imp_false(α.[x]);
		done;
	- for ι α P, if 1: nnot_ex ι (x. α.[x]), all: (∀x. α.[x] ⟹ ι x ⟹ P), ta! ∀x. ι x ⟹ image_nnot α.[x], tP! image_nnot P then P :=
		fold tP[unfolded image_nnot_iff];
		apply not_intro;
		- if nP: ¬P :=
			have 2: ¬(∀x:ι. ¬α.[x]) :=
				by 1[unfolded nnot_ex_iff];
			apply not_elim[OF 2];
			apply all_intro;
			- for x, if [ι x] then ¬ α.[x] :=
				apply not_intro;
				- if ax: α.[x] :=
					have P: P :=
						by all[OF ax];
					by not_imp_false[OF nP P];
				done;
			done;
		done;
	- for P, if f: false, tP! image_nnot P :=
		apply false_elim[OF f];
		done;
	- for P, if tP! image_nnot P then nnot_or P (¬ P) :=
		unfold nnot_or_iff;
		by non_contradiction;
	done;


thm image_nnot.pierce_law;

