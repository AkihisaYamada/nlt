------
# Gödel―Gentzen Negative Translation
------

----
The intuitionistic logic can prove theorems of the classical logic after a double-negation translation.
To formally state the result, we interpret the classical logic context, replacing the `Prop` type of by the image of double negation,
disjunction and existential quantifier by certain forms.

Since we have not introduced convenient methods such as equality to specify such, we use axioms to do so.
----
import Eq.
import Minimal.
import FirstOrder.
print.

assume in_DN_iff: P ∈ DN ⟺ (∃P' ∈ Prop. P = (¬¬P')).

--The negative translation of disjunction is specified as follows.
fix nnot_or.
assume nnot_or_def: nnot_or P Q = (¬(¬P ∧ ¬Q)).

-- The existential quantifier is translated as follows:
fix nnot_ex.
assume nnot_ex_def: nnot_ex A (x. Y.[x]) = (¬(∀x ∈ A. ¬Y.[x])).

begin

interpret nnot_or: Magma Prop nnot_or;
	by #unfold nnot_or_def.

lemma nnot_ex_type:
	if A! A ∈ QTYPE, ! ∀x. x ∈ A ⟹ Y.[x] ∈ Prop
	then nnot_ex A (x. Y.[x]) ∈ Prop;
	unfold nnot_ex_def.

--note! nnot_or.type.
--note! nnot_ex.type.
lemma DN_imp_Prop: P ∈ DN ⟹ P ∈ Prop;
	unfold in_DN_iff;.
---
lemma DN_iff: if [P ∈ Prop] then P ∈ DN ⟺ (¬¬P ⟺ P);
	apply iff_intro;
	- if tP! P ∈ DN then ¬¬P ⟺ P;
		apply in.ex_elim[OF tP[unfolded in_DN_iff]];
		- for P' if ! P' ∈ Prop, eq: P = (¬¬P');
			unfold+ eq nnnot_iff.
		.
	- if nn: ¬¬P ⟺ P then P ∈ DN;
		unfold in_DN_iff;
		apply in.ex_intro;
		- for thesis if assm;
			by assm[of P] #unfold nn.
		.
	.
---
----
## Proving that the image of double negation and operators satisfy the classical logic axioms.
----

interpret DN: Typed;
goals.
	instantiate (∨) := nnot_or, (∃∈) := nnot_ex, Prop := DN.
	- unfold in_DN_iff not_true_iff not_false_iff.
	- .
	- unfold DN_iff not_true_iff not_false_iff.
	- for P Q, if tP! DN P, tQ! DN Q then DN (P ⟹ Q);
		have nnQ: ¬¬Q ⟺ Q;
			by tQ[unfolded DN_iff].
		unfold DN_iff,
		fold nnQ,
		unfold nnimp_not_iff.
	- for P, if tP: DN P then DN (¬P);
		note! DN_imp_Prop[OF tP].
		unfold DN_iff tP[unfolded DN_iff] nnnot_iff.
	- for P, if P0: P ⟹ false, tP: DN P then ¬P;
		by not_intro[OF P0] DN_imp_Prop[OF tP].
	- for P, if nP: ¬P, P: P, tP: DN P then false;
		by not_imp_false[OF nP P] DN_imp_Prop[OF tP].
	- for P Q, if tP: DN P, tQ: DN Q then DN (P ∧ Q);
		note! DN_imp_Prop[OF tP].
		note! DN_imp_Prop[OF tQ].
		unfold+ DN_iff nnand_iff,
		unfold tP[unfolded DN_iff] tQ[unfolded DN_iff].
	- by and_intro DN_imp_Prop.
	- by DN_imp_Prop #elim and_elim.
	- by DN_imp_Prop #elim and_elim.
	- for P Q, if tP! DN P, tQ! DN Q then DN (P ⟺ Q);
		unfold DN_iff,
		fold tP[unfolded DN_iff],
		fold tQ[unfolded DN_iff],
		unfold nniff_iff.
	- by iff_intro DN_imp_Prop.
	- by DN_imp_Prop #elim iff_elim1.
	- by DN_imp_Prop #elim iff_elim2.
	- for P Q, if tP! DN P, tQ! DN Q then DN (nnot_or P Q);
		unfold DN_iff nnot_or_iff nnnot_iff.
	- for P Q, if P: P;
		by #unfold+ nnot_or_iff iff_true[OF P] not_true_iff false_and_iff not_false_iff.
	- for P Q, if Q: Q;
		by #unfold+ nnot_or_iff iff_true[OF Q] not_true_iff and_false_iff not_false_iff.
	- for P Q, if 1: nnot_or P Q;
		- for R, if PR: P ⟹ R, QR: Q ⟹ R,
			tP! DN P, tQ! DN Q, tR! DN R then R;
			fold tR[unfolded DN_iff],
			apply not_intro,
			- if nR: ¬R;
				have 2: ¬(¬P ∧ ¬Q);
					by 1[unfolded nnot_or_iff].
				apply not_elim[OF 2],
				apply and_intro,
				by imp_not_imp[OF PR nR] imp_not_imp[OF QR nR].
			.
		.
	- for ι α, if ta! ∀x. ι x ⟹ DN α.[x] then DN (∀x:ι. α.[x]);
		unfold DN_iff,
		have nna: for x, if xt! ι x then α.[x] ⟺ (¬¬α.[x]);
			unfold ta[OF xt][unfolded DN_iff].
		unfold nna,
		unfold nnall_not_iff.
	- by all_intro #force.
	- for x ι α, if all: ∀y:ι. α.[y], [∀y. ι y ⟹ DN α.[y], ι x] then α.[x];
		apply all_elim[OF all].
	- for ι α, if ta! ∀x. ι x ⟹ DN α.[x] then DN (nnot_ex ι (x. α.[x]));
		unfold DN_iff,
		unfold nnot_ex_iff nnnot_iff.
	- for x α ι, if [α.[x], ι x], ta! ∀y. ι y ⟹ DN α.[y] then nnot_ex ι (z. α.[z]);
		unfold nnot_ex_iff,
		apply not_intro,
		- if an: ∀y:ι. ¬α.[y];
			apply all_elim[OF an],
			by not_imp_false(α.[x]).
		.
	- for ι α, if 1: nnot_ex ι (x. α.[x]);
		- for P, if all: (∀x. α.[x] ⟹ ι x ⟹ P),
			ta! ∀x. ι x ⟹ DN α.[x],
			tP! DN P
		  then P;
			fold tP[unfolded DN_iff],
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
	show: false ⟹ ∀P. DN P ⟹ P;
		by #elim false_elim.
	- for P, if tP! DN P then nnot_or P (¬ P);
		unfold nnot_or_iff,
		by non_contradiction.
	.


thm DN.pierce_law.

