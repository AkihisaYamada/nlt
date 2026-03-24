------
# Gödel―Gentzen Negative Translation
------

---
Intuitionistic (minimal) logic can prove theorems of classical logic after a double-negation translation.
To formally state the result, in (type-free) minimal logic we interpret typed classical logic, where propositions are those admitting double negation elimination,
disjunction and existential quantifier are instantiated by certain forms.
---
import TypeFree.
import Minimal.
import in: Minimal.AllRel (∈) (∀∈).

fix nnProp nnor nnex nnexIn.
assume in_nnProp_iff: P ∈ nnProp ⟺ (¬ ¬P ⟹ P).

--The negative translation of disjunction is specified as follows.
assume nnor_def: nnor P Q ⟺ ¬(¬P ∧ ¬Q).

-- The existential quantifier is translated as follows:
assume nnex_def: nnex (x. Y.[x]) ⟺ ¬(∀x. ¬ Y.[x]).

assume nnexIn_def: nnexIn A (x. Y.[x]) ⟺ ¬(∀x ∈ A. ¬ Y.[x]).

begin
thy.
lemma nnProp_imp_nnot: P ∈ nnProp ⟹ ¬ ¬P ⟺ P;
	by iff_intro nnot_intro #simp in_nnProp_iff.

lemma in_nnProp_intro: if nn: ¬ ¬P ⟹ P then P ∈ nnProp;
	by nn #simp in_nnProp_iff.

----
## Proving that the image of double negation and operators satisfy the classical logic axioms.
----

note#cong in.all_cong_weak.

interpret nnProp: FreeOrder;
	instantiate Prop := nnProp, (∨) := nnor, (∃∈) := nnexIn.
	- if ! P ∈ nnProp, ! Q ∈ nnProp then (P ⟹ Q) ∈ nnProp;
		unfold in_nnProp_iff;
		fold nnProp_imp_nnot;
		simp nnimp_not_iff.
	- if ! P ∈ nnProp, ! Q ∈ nnProp then (P ∧ Q) ∈ nnProp;
		unfold in_nnProp_iff;
		simp nnand_iff nnProp_imp_nnot.
	- if ! P ∈ nnProp, ! Q ∈ nnProp then nnor P Q ∈ nnProp;
		unfold in_nnProp_iff;
		unfold nnor_def;
		simp nnnot_iff.
	- if ! P ∈ nnProp then (¬P) ∈ nnProp;
		unfold in_nnProp_iff;
		simp nnnot_iff.
	- if ! P ∈ nnProp, ! Q ∈ nnProp then (P ⟺ Q) ∈ nnProp;
		unfold in_nnProp_iff;
		fold nnProp_imp_nnot;
		simp not_nniff_not.
	- if ! ∀x. x ∈ A ⟹ P.[x] ∈ nnProp then (∀x ∈ A. P.[x]) ∈ nnProp;
		unfold in_nnProp_iff;
		fold nnProp_imp_nnot;
		unfold in.nnall_not_iff;
		simp nnProp_imp_nnot.
	- if ! ∀x. x ∈ A ⟹ P.[x] ∈ nnProp then nnexIn A (x. P.[x]) ∈ nnProp;
		unfold in_nnProp_iff;
		unfold nnexIn_def;
		simp nnnot_iff.
	retain false;
		by #simp in_nnProp_iff.
	retain true;
		by #simp in_nnProp_iff.
	.

interpret nnProp: nnProp.Classical;
	instantiate (∃) := nnex.
	- for P Q if !P then nnor P Q;
		unfold nnor_def;
		simp imp_not_iff_false false_nand[THEN iff_true].
	- for P Q if !Q then nnor P Q;
		unfold nnor_def;
		simp imp_not_iff_false nand_false[THEN iff_true].
	- for x if Px: P.[x] then nnex (x. P.[x]);
		simp nnex_def;
		apply not_intro;
		- if all: ∀x. ¬ P.[x] then false;
			by not_imp_false[OF all Px].
		.
	- if or: nnor P Q, ! R ∈ nnProp, PR: P ⟹ R, QR: Q ⟹ R then R;
		have nnR: ¬ ¬R;
			apply not_intro;
			- if nR: ¬R then false;
				apply+ or[unfold nnor_def, THEN not_imp_false] and_intro not_intro;
				- if P: P then false;
					by not_imp_false[OF nR PR[OF P]].
				- if Q: Q then false;
					by not_imp_false[OF nR QR[OF Q]].
				.
			.
		by nnR[unfold nnProp_imp_nnot].
	- if ex: nnex (x. P.[x]), imp: ∀x. P.[x] ⟹ Q, ! Q ∈ nnProp then Q;
		have nnQ: ¬ ¬Q;
			apply not_intro;
			- if nQ: ¬Q then false;
				apply+ ex[unfold nnex_def, THEN not_imp_false];
				-> if Px: P.[x];
					apply not_imp_false[OF nQ imp[OF Px]].
				.
			.
		by nnQ[unfold nnProp_imp_nnot].
	- if 0: false, ! P ∈ nnProp then P;
		have nnP: ¬ ¬P;
			by not_intro 0.
		by nnP[unfold nnProp_imp_nnot].
	- if ! P ∈ nnProp then nnor P (¬P);
		unfold nnor_def;
		by non_contradiction.
	- by in.all_intro.
	- by #elim in.all_elim.
	- show: nnexIn A (x. P.[x]) ⟺ nnex (x. x ∈ A ∧ P.[x]);
		unfold nnexIn_def nnex_def in.all_def imp_not_iff_nand;.
	.

thm nnProp.pierce_law.
