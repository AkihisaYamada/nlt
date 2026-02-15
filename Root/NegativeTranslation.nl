------
# Gödel―Gentzen Negative Translation
------

----
The intuitionistic logic can prove theorems of the classical logic after a double-negation translation.
To formally state the result, we interpret the classical logic context, replacing the `Prop` type of by the image of double negation,
disjunction and existential quantifier by certain forms.

We import equality to denote the definitions of disjunction and existential quantifier.
----
import Eq.
import Minimal.
import FirstOrder.
print.

fix DN.
assume in_DN_iff: P ∈ DN ⟺ P ∈ Prop ∧ ((¬¬P) ⟺ P).

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

lemma DN_imp_Prop(simp) P ∈ DN ⟹ P ∈ Prop ⟺ true;
	simp in_DN_iff.

lemma DN_imp_nnot: P ∈ DN ⟹ ¬¬P ⟺ P;
	unfold in_DN_iff.

lemma in_DN_intro: if nn: (¬¬P) ⟺ P, ! P ∈ Prop then P ∈ DN;
	simp in_DN_iff nn.

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
	instantiate Prop := DN.
	- if ! P ∈ DN, ! Q ∈ DN then (P ⟹ Q) ∈ DN;
		apply in_DN_intro;
		fold DN_imp_nnot;
		simp nnimp_not_iff.
	- then false ∈ DN;
		apply in_DN_intro.
	- if ! P ∈ DN, ! Q ∈ DN then (P ⟺ Q) ∈ DN;
		apply in_DN_intro;
		fold DN_imp_nnot;
		simp not_nniff_not.
	- if ! P ∈ DN, ! Q ∈ DN then (P ∧ Q) ∈ DN;
		apply in_DN_intro;
		simp nnand_iff DN_imp_nnot.
	- if ! P ∈ DN then (¬P) ∈ DN;
		apply in_DN_intro;
		simp nnnot_iff.
	- if ! A ∈ QTYPE, ! ∀x. x ∈ A ⟹ P.[x] ∈ DN then (∀x ∈ A. P.[x]) ∈ DN;
		apply in_DN_intro;
		fold DN_imp_nnot;
		unfold in.nnall_not_iff;
		simp DN_imp_nnot.
	instantiate (∨) := nnot_or.
	- for P Q if !P then nnot_or P Q;
		unfold nnot_or_def;
		simp imp_not_iff_false false_nand[THEN iff_true].
	- for P Q if !Q then nnot_or P Q;
		unfold nnot_or_def;
		simp imp_not_iff_false nand_false[THEN iff_true].
	- if or: nnot_or P Q, ! R ∈ DN, PR: P ⟹ R, QR: Q ⟹ R then R;
		have nnR: ¬¬R;
			apply not_intro;
			- if nR: ¬R then false;
				apply+ or[unfold nnot_or_def, THEN not_imp_false] and_intro not_intro;
				- if P: P then false;
					by not_imp_false[OF nR PR[OF P]].
				- if Q: Q then false;
					by not_imp_false[OF nR QR[OF Q]].
				.
			.
		by nnR[unfold DN_imp_nnot].
	- if ! P ∈ DN, ! Q ∈ DN then nnot_or P Q ∈ DN;
		unfold nnot_or_def;
		apply in_DN_intro;
		simp nnnot_iff.
	instantiate (∃∈) := nnot_ex.
	- if ! x ∈ A, Px: P.[x] then nnot_ex A (x. P.[x]);
		simp nnot_ex_def;
		apply not_intro;
		- if all: ∀x ∈ A. ¬ P.[x] then false;
			have nPx: ¬ P.[x];
				by all[THEN in.all_elim1].
			by not_imp_false[OF nPx Px].
		.
	- if ex: nnot_ex A (x. P.[x]), imp: ∀x. x ∈ A ⟹ P.[x] ⟹ Q, ! Q ∈ DN then Q;
		have nnQ: ¬¬Q;
			apply not_intro;
			- if nQ: ¬Q then false;
				apply+ ex[unfold nnot_ex_def, THEN not_imp_false] in.all_intro;
				- if x: x ∈ A then ¬ P.[x];
					apply not_intro;
					- if Px: P.[x];
						apply not_imp_false[OF nQ imp[OF x Px]].
					.
				.
			.
		by nnQ[unfold DN_imp_nnot].
	- if ! A ∈ QTYPE, ! ∀x. x ∈ A ⟹ P.[x] ∈ DN then nnot_ex A (x. P.[x]) ∈ DN;
		unfold nnot_ex_def;
		apply in_DN_intro;
		simp nnnot_iff.
	.

thm DN.pierce_law.

