------
# Gödel―Gentzen Negative Translation
------

----
The intuitionistic logic can prove theorems of the classical logic after a double-negation translation.
To formally state the result, we interpret the classical logic context, replacing the `Prop` type of by the image of double negation,
disjunction and existential quantifier by certain forms.

Since we have not introduced convenient methods such as equality to specify such, we use axioms to do so.
----

import Lambda.

set define beta.

import FOL.

import Intuitionistic.
print.
thy.
define image_nnot P := ∃P'. P' ∈ Prop ∧ P = (¬¬P').

lemma image_nnot_imp_Prop: if P: image_nnot P then P ∈ Prop;
	apply P[unfolded image_nnot_def, THEN ex_elim];


assume image_nnot_iff_ex: P ∈ Prop ⟹ image_nnot P ⟺ (∃P' ∈ Prop. P ⟺ ¬¬P').

--The negative translation of disjunction is specified as follows.

assume nnot_or_iff: nnot_or P Q ⟺ ¬(¬P ∧ ¬Q).

---
In this context, it is necessary to assume that this operation is well-typed.
We should be able to derive the fact if we introduce equality and definition.
---
assume nnot_or_type! Prop P ⟹ Prop Q ⟹ Prop (nnot_or P Q).
--import nnot_or: Magma Prop nnot_or.

-- The existential quantifier is translated as follows:

assume nnot_ex_iff: nnot_ex ι (x. Y.[x]) ⟺ ¬(∀x:ι. ¬Y.[x]).

assume nnot_ex_type! (∀x. ι x ⟹ Prop Y.[x]) ⟹ Prop (nnot_ex ι (x. Y.[x])).

begin

--note! nnot_or.type.
--note! nnot_ex.type.
note? image_nnot_imp_Prop.

----
## Proving that the image of double negation and operators satisfy the classical logic axioms.
----

interpret image_nnot: ClassicalLogic;
	instantiate Prop := image_nnot, (∨) := nnot_or, (∃:) := nnot_ex.

	have image_nnot_iff: if [Prop P] then image_nnot P ⟺ (¬¬P ⟺ P);
		apply iff_intro,
		- if tP! image_nnot P then ¬¬P ⟺ P;
			apply ex_elim[OF tP[unfolded image_nnot_iff_ex]],
			- for P', if iff: (P ⟺ ¬¬P'), [Prop P'];
				unfold+ iff nnnot_iff.
			.
		- if nn: ¬¬P ⟺ P then image_nnot P;
			unfold image_nnot_iff_ex,
			apply ex_intro,
			- for P', if imp: ∀x. (P ⟺ ¬¬x) ⟹ Prop x ⟹ P', [Prop P'];
				by imp(P) #unfold nn.
			.
		.
	- unfold image_nnot_iff not_true_iff not_false_iff.
	- .
	- unfold image_nnot_iff not_true_iff not_false_iff.
	- for P Q, if tP! image_nnot P, tQ! image_nnot Q then image_nnot (P ⟹ Q);
		have nnQ: ¬¬Q ⟺ Q;
			by tQ[unfolded image_nnot_iff].
		unfold image_nnot_iff,
		fold nnQ,
		unfold nnimp_not_iff.
	- for P, if tP: image_nnot P then image_nnot (¬P);
		note! image_nnot_imp_Prop[OF tP].
		unfold image_nnot_iff tP[unfolded image_nnot_iff] nnnot_iff.
	- for P, if P0: P ⟹ false, tP: image_nnot P then ¬P;
		by not_intro[OF P0] image_nnot_imp_Prop[OF tP].
	- for P, if nP: ¬P, P: P, tP: image_nnot P then false;
		by not_imp_false[OF nP P] image_nnot_imp_Prop[OF tP].
	- for P Q, if tP: image_nnot P, tQ: image_nnot Q then image_nnot (P ∧ Q);
		note! image_nnot_imp_Prop[OF tP].
		note! image_nnot_imp_Prop[OF tQ].
		unfold+ image_nnot_iff nnand_iff,
		unfold tP[unfolded image_nnot_iff] tQ[unfolded image_nnot_iff].
	- by and_intro image_nnot_imp_Prop.
	- by image_nnot_imp_Prop #elim and_elim.
	- by image_nnot_imp_Prop #elim and_elim.
	- for P Q, if tP! image_nnot P, tQ! image_nnot Q then image_nnot (P ⟺ Q);
		unfold image_nnot_iff,
		fold tP[unfolded image_nnot_iff],
		fold tQ[unfolded image_nnot_iff],
		unfold nniff_iff.
	- by iff_intro image_nnot_imp_Prop.
	- by image_nnot_imp_Prop #elim iff_elim1.
	- by image_nnot_imp_Prop #elim iff_elim2.
	- for P Q, if tP! image_nnot P, tQ! image_nnot Q then image_nnot (nnot_or P Q);
		unfold image_nnot_iff nnot_or_iff nnnot_iff.
	- for P Q, if P: P;
		by #unfold+ nnot_or_iff iff_true[OF P] not_true_iff false_and_iff not_false_iff.
	- for P Q, if Q: Q;
		by #unfold+ nnot_or_iff iff_true[OF Q] not_true_iff and_false_iff not_false_iff.
	- for P Q, if 1: nnot_or P Q;
		- for R, if PR: P ⟹ R, QR: Q ⟹ R,
			tP! image_nnot P, tQ! image_nnot Q, tR! image_nnot R then R;
			fold tR[unfolded image_nnot_iff],
			apply not_intro,
			- if nR: ¬R;
				have 2: ¬(¬P ∧ ¬Q);
					by 1[unfolded nnot_or_iff].
				apply not_elim[OF 2],
				apply and_intro,
				by imp_not_imp[OF PR nR] imp_not_imp[OF QR nR].
			.
		.
	- for ι α, if ta! ∀x. ι x ⟹ image_nnot α.[x] then image_nnot (∀x:ι. α.[x]);
		unfold image_nnot_iff,
		have nna: for x, if xt! ι x then α.[x] ⟺ (¬¬α.[x]);
			unfold ta[OF xt][unfolded image_nnot_iff].
		unfold nna,
		unfold nnall_not_iff.
	- by all_intro #force.
	- for x ι α, if all: ∀y:ι. α.[y], [∀y. ι y ⟹ image_nnot α.[y], ι x] then α.[x];
		apply all_elim[OF all].
	- for ι α, if ta! ∀x. ι x ⟹ image_nnot α.[x] then image_nnot (nnot_ex ι (x. α.[x]));
		unfold image_nnot_iff,
		unfold nnot_ex_iff nnnot_iff.
	- for x α ι, if [α.[x], ι x], ta! ∀y. ι y ⟹ image_nnot α.[y] then nnot_ex ι (z. α.[z]);
		unfold nnot_ex_iff,
		apply not_intro,
		- if an: ∀y:ι. ¬α.[y];
			apply all_elim[OF an],
			by not_imp_false(α.[x]).
		.
	- for ι α, if 1: nnot_ex ι (x. α.[x]);
		- for P, if all: (∀x. α.[x] ⟹ ι x ⟹ P),
			ta! ∀x. ι x ⟹ image_nnot α.[x],
			tP! image_nnot P
		  then P;
			fold tP[unfolded image_nnot_iff],
			apply not_intro,
			- if nP: ¬P;
				have 2: ¬(∀x:ι. ¬α.[x]);
					by 1[unfolded nnot_ex_iff].
				apply not_elim[OF 2],
				apply all_intro,
				- for x, if [ι x] then ¬ α.[x];
					apply not_intro,
					- if ax: α.[x];
						have P: P;
							by all[OF ax].
						by not_imp_false[OF nP P].
					.
				.
			.
		.
	show: false ⟹ ∀P. image_nnot P ⟹ P;
		by #elim false_elim.
	- for P, if tP! image_nnot P then nnot_or P (¬ P);
		unfold nnot_or_iff,
		by non_contradiction.
	.


thm image_nnot.pierce_law.

