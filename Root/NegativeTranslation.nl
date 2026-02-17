------
# Gödel―Gentzen Negative Translation
------

----
The intuitionistic logic can prove theorems of the classical logic after a double-negation translation.
To formally state the result, we interpret the classical logic context, replacing the `Prop` type of by the image of double negation,
disjunction and existential quantifier by certain forms.

We import equality to denote the definitions of disjunction and existential quantifier.
----
print.
import Eq.
import Minimal.
import Minimal.Membership.

thm in.all_def.

fix DN.
assume in_DN_iff: P ∈ DN ⟺ ((¬¬P) ⟺ P).

--The negative translation of disjunction is specified as follows.
fix nnor.
assume nnor_def: nnor P Q = (¬(¬P ∧ ¬Q)).

-- The existential quantifier is translated as follows:
fix nnex.
assume nnex_def: nnex (x. Y.[x]) = (¬(∀x. ¬Y.[x])).

fix nnexIn.
assume nnexIn_def: nnexIn A (x. Y.[x]) = (¬(∀x ∈ A. ¬Y.[x])).

begin

lemma DN_imp_nnot: P ∈ DN ⟹ ¬¬P ⟺ P;
	unfold in_DN_iff.

lemma in_DN_intro: if nn: (¬¬P) ⟺ P then P ∈ DN;
	simp in_DN_iff nn.

----
## Proving that the image of double negation and operators satisfy the classical logic axioms.
----

namespace DN:

interpret Root.Typed;
	instantiate Prop := DN.
	- if ! P ∈ DN, ! Q ∈ DN then (P ⟹ Q) ∈ DN;
		apply in_DN_intro;
		fold DN_imp_nnot;
		simp nnimp_not_iff.
	.
interpret FreeOrder;
	- if ! ∀x. x ∈ A ⟹ P.[x] ∈ DN then (∀x ∈ A. P.[x]) ∈ DN;
		apply in_DN_intro;
		fold DN_imp_nnot;
		unfold in.nnall_not_iff;
		simp DN_imp_nnot.
	instantiate (∃∈) := nnexIn.
	- if ! ∀x. x ∈ A ⟹ P.[x] ∈ DN then nnexIn A (x. P.[x]) ∈ DN;
		unfold nnexIn_def;
		apply in_DN_intro;
		simp nnnot_iff.
	retain false;
		by in_DN_intro.
	retain true;
		by in_DN_intro.
	- if ! P ∈ DN, ! Q ∈ DN then (P ∧ Q) ∈ DN;
		apply in_DN_intro;
		simp nnand_iff DN_imp_nnot.
	instantiate (∨) := nnor.
	- if ! P ∈ DN, ! Q ∈ DN then nnor P Q ∈ DN;
		unfold nnor_def;
		apply in_DN_intro;
		simp nnnot_iff.
	- if ! P ∈ DN then (¬P) ∈ DN;
		apply in_DN_intro;
		simp nnnot_iff.
	- if ! P ∈ DN, ! Q ∈ DN then (P ⟺ Q) ∈ DN;
		apply in_DN_intro;
		fold DN_imp_nnot;
		simp not_nniff_not.
	.

thm ex_type.

interpret FreeOrder.Classical;
	goals.
	- for P Q if !P then nnor P Q;
		unfold nnor_def;
		simp imp_not_iff_false false_nand[THEN iff_true].
	- for P Q if !Q then nnor P Q;
		unfold nnor_def;
		simp imp_not_iff_false nand_false[THEN iff_true].
	instantiate (∃) := nnex.
	- for x if Px: P.[x] then nnex (x. P.[x]);
		simp nnex_def;
		apply not_intro;
		- if all: ∀x. ¬ P.[x] then false;
			by not_imp_false[OF all Px].
		.
	- then nnexIn A (x. P.[x]) ⟺ nnex (x. x ∈ A ∧ P.[x]);
		unfold nnexIn_def nnex_def in.all_def imp_not_iff_nand;.
	- if or: nnor P Q, ! R ∈ DN, PR: P ⟹ R, QR: Q ⟹ R then R;
		have nnR: ¬¬R;
			apply not_intro;
			- if nR: ¬R then false;
				apply+ or[unfold nnor_def, THEN not_imp_false] and_intro not_intro;
				- if P: P then false;
					by not_imp_false[OF nR PR[OF P]].
				- if Q: Q then false;
					by not_imp_false[OF nR QR[OF Q]].
				.
			.
		by nnR[unfold DN_imp_nnot].
	- if ex: nnex (x. P.[x]), imp: ∀x. P.[x] ⟹ Q, ! Q ∈ DN then Q;
		have nnQ: ¬¬Q;
			apply not_intro;
			- if nQ: ¬Q then false;
				apply+ ex[unfold nnex_def, THEN not_imp_false];
				- then ¬ P.[x];
					apply not_intro;
					- if Px: P.[x];
						apply not_imp_false[OF nQ imp[OF Px]].
					.
				.
			.
		by nnQ[unfold DN_imp_nnot].	- if 0: false, ! P ∈ DN then P;
		have nnP: ¬¬P;
			by not_intro 0.
		by nnP[unfold DN_imp_nnot].
	- if ! P ∈ DN then nnor P (¬ P);
		unfold nnor_def;
		by non_contradiction.
	.
end

thm DN.pierce_law DN.excluded_middle.


thm DN.in.ex_def.

end
