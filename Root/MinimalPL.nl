---
# Minimal Propositional Logic
---
import Base.

---
## Axiomatization
---

fix (:) PROP true false (¬) (∧) (∨) (⟺).

assume true_type! true ∈ PROP.
assume false_type! false ∈ PROP.
assume imp_type! P ∈ PROP ⟹ Q ∈ PROP ⟹ (P ⟹ Q) ∈ PROP.
assume not_type! P ∈ PROP ⟹ (¬ P) ∈ PROP.
assume and_type! P ∈ PROP ⟹ Q ∈ PROP ⟹ (P ∧ Q) ∈ PROP.
assume  or_type! P ∈ PROP ⟹ Q ∈ PROP ⟹ (P ∨ Q) ∈ PROP.
assume iff_type! P ∈ PROP ⟹ Q ∈ PROP ⟹ (P ⟺ Q) ∈ PROP.

assume true_intro! true.
assume not_intro: (P ⟹ false) ⟹ P ∈ PROP ⟹ ¬P.
assume not_imp_false: ¬P ⟹ P ⟹ P ∈ PROP ⟹ false.
assume and_intro: P ⟹ Q ⟹ P ∈ PROP ⟹ Q ∈ PROP ⟹ P ∧ Q.
assume and_elim1: P ∧ Q ⟹ P ∈ PROP ⟹ Q ∈ PROP ⟹ P.
assume and_elim2: P ∧ Q ⟹ P ∈ PROP ⟹ Q ∈ PROP ⟹ Q.
assume or_intro1: P ⟹ P ∈ PROP ⟹ Q ∈ PROP ⟹ P ∨ Q.
assume or_intro2: ∀ P Q. Q ⟹ P ∈ PROP ⟹ Q ∈ PROP ⟹ P ∨ Q.
assume or_elim: P ∨ Q ⟹ ∀R. (P ⟹ R) ⟹ (Q ⟹ R) ⟹ P ∈ PROP ⟹ Q ∈ PROP ⟹ R ∈ PROP ⟹ R.

assume iff_intro: (P ⟹ Q) ⟹ (Q ⟹ P) ⟹ P ∈ PROP ⟹ Q ∈ PROP ⟹ (P ⟺ Q).
assume iff_elim1: (P ⟺ Q) ⟹ P ⟹ P ∈ PROP ⟹ Q ∈ PROP ⟹ Q.
assume iff_elim2: (P ⟺ Q) ⟹ Q ⟹ P ∈ PROP ⟹ Q ∈ PROP ⟹ P.

begin

---
## Theorems
---
interpret TypedIff.

lemma not_false: ¬false;
	apply not_intro.

----
### True, False, and Negation
----

lemma iff_true: if [P, P ∈ PROP] then P ⟺ true;
	by iff_intro.

set to_true iff_true.

lemma true_imp_iff: if [P ∈ PROP] then (true ⟹ P) ⟺ P;
	by imp_imp_iff.

lemma imp_true_iff: if [P ∈ PROP] then (P ⟹ true) ⟺ true;
	by iff_intro.

lemma iff_cong_not#cong: if PP': P ⟺ P', [P ∈ PROP, P' ∈ PROP] then ¬P ⟺ ¬P';
	apply iff_intro;
	if nP: ¬P;
		apply not_intro;
		by not_imp_false[OF nP] iff_elim2[OF PP'].
	if nP': ¬P';
		apply not_intro;
		by not_imp_false[OF nP'] iff_elim1[OF PP'].
	.

lemma not_iff_imp_false: if [P ∈ PROP] then ¬P ⟺ (P ⟹ false);
	apply iff_intro;
	if nP: ¬P;
		by not_imp_false[OF nP].
	if Pf: P ⟹ false;
		by not_intro Pf.
	.

lemma not_true_iff: ¬true ⟺ false;
	unfold not_iff_imp_false true_imp_iff.

lemma nnot_intro: if P: P, [P ∈ PROP] then ¬¬P;
	unfold P not_true_iff not_false.

lemma nnot_imp: if imp: ¬¬P ⟹ Q, [P, P ∈ PROP] then Q;
	by imp nnot_intro.

lemma imp_not: if P: P, [¬Q, P ∈ PROP, Q ∈ PROP] then ¬(P ⟹ Q);
	unfold P true_imp_iff.

lemma imp_not_imp: if PQ: P ⟹ Q, nQ: ¬Q, [P ∈ PROP, Q ∈ PROP] then ¬P;
	apply not_intro;
	by not_imp_false[OF nQ] PQ.

lemma imp_not_sym: if PnQ: P ⟹ ¬Q, Q: Q, [P ∈ PROP, Q ∈ PROP] then ¬P;
	by not_intro PnQ[unfolded Q not_true_iff].

lemma nnot_imp_nnot: if nnP: ¬¬P, PQ: P ⟹ Q, [P ∈ PROP, Q ∈ PROP] then ¬¬Q;
	apply not_intro;
	if nQ: ¬Q;
		have nP: ¬P;
			by imp_not_imp[OF PQ nQ].
		by not_imp_false[OF nnP] nP.
	.

lemma nnimp_imp_nnot: if nnPQ: ¬¬(P ⟹ Q), P: P, [P ∈ PROP, Q ∈ PROP] then ¬¬Q;
	by nnPQ[unfolded P true_imp_iff].

lemma nnot_not_imp_nimp: if nnP: ¬¬P, nQ: ¬Q, [P ∈ PROP, Q ∈ PROP] then ¬(P ⟹ Q);
	apply not_intro;
	if PQ: P ⟹ Q;
		have nnQ: ¬¬Q;
			by nnot_imp_nnot[OF nnP] PQ.
		by not_imp_false[OF nnQ nQ].
	.

theorem nnnot_iff: if [P ∈ PROP] then ¬¬¬P ⟺ ¬P;
	unfold+ not_iff_imp_false imp3_iff.

lemma imp_not_commute: if [P ∈ PROP, Q ∈ PROP] then
	(P ⟹ ¬Q) ⟺ (Q ⟹ ¬P);
	by iff_intro #elim imp_not_sym.

lemma nnot_imp_not_iff: if [P ∈ PROP, Q ∈ PROP] then
	(¬¬P ⟹ ¬Q) ⟺ (P ⟹ ¬Q);
	unfold imp_not_commute;
	unfold nnnot_iff.

lemma nnimp_not_iff: if [P ∈ PROP, Q ∈ PROP] then
	¬¬(P ⟹ ¬Q) ⟺ (P ⟹ ¬Q);
	apply iff_intro;
	if nnimp: ¬¬(P ⟹ ¬Q), P: P then ¬Q;
		by nnimp[unfolded P true_imp_iff nnnot_iff].
	by nnot_intro.

---
### Conjunction
---

lemma and_elim: if and: P ∧ Q then
	∀R. (P ⟹ Q ⟹ R) ⟹ P ∈ PROP ⟹ Q ∈ PROP ⟹ R;
	for R if PQR: P ⟹ Q ⟹ R;
		by PQR and_elim1[OF and] and_elim2[OF and].
	.

namespace and begin

interpret PartialEquivalence prop (∧);
	by and_intro #elim and_elim.

interpret AbsorbMonoid prop (∧) false true;
	goals.

end

lemma iff_cong_and#cong: for P Q
	if PP': P ⟺ P', QQ': Q ⟺ Q', [P ∈ PROP, Q ∈ PROP, P' ∈ PROP, Q' ∈ PROP]
	then P ∧ Q ⟺ P' ∧ Q';
	apply iff_intro;
	- by and_intro #fold PP' QQ' #elim and_elim.
	- by and_intro #unfold PP' QQ' #elim and_elim.
	.

interpret and: Magma prop (∧).
interpret and: Relation prop (∧).

interpret and_iff: Commutative prop (∧) (⟺);
	by iff_intro and_intro #elim and_elim.

interpret and_iff: Associative prop (∧) (⟺);
	by iff_intro and_intro #elim and_elim.

lemma true_and_iff: if [P ∈ PROP] then true ∧ P ⟺ P;
	by iff_intro and_intro #elim and_elim.

lemma iff_imp_and: if PQ: P ⟺ Q, [P ∈ PROP, Q ∈ PROP] then (P ⟹ Q) ∧ (Q ⟹ P);
	by and_intro #unfold PQ.

lemma iff_iff_and: if [P ∈ PROP, Q ∈ PROP] then (P ⟺ Q) ⟺ (P ⟹ Q) ∧ (Q ⟹ P);
	by iff_intro and_intro #elim iff_elim and_elim.

lemma and_imp_iff: if [P ∈ PROP, Q ∈ PROP, R ∈ PROP] then
	(P ∧ Q ⟹ R) ⟺ (P ⟹ Q ⟹ R);
	by iff_intro and_intro #elim and_elim.

lemma true_and_true: true ∧ true;
	unfold true_and_iff.

lemma and_true_iff: if [P ∈ PROP] then P ∧ true ⟺ P;
	unfold and_iff.commute;
	unfold true_and_iff.

lemma iff_iff_and: if [P ∈ PROP, Q ∈ PROP] then
	(P ⟺ Q) ⟺ (P ⟹ Q) ∧ (Q ⟹ P);
	by iff_intro and_intro #elim iff_elim and_elim.

lemma nand_intro1: if nP: ¬P, [P ∈ PROP, Q ∈ PROP] then ¬(P ∧ Q);
	apply not_intro;
	if PQ: P ∧ Q then false;
		by not_imp_false[OF nP] and_elim1[OF PQ].
	.

lemma nand_intro2: for P Q if nQ: ¬Q, [P ∈ PROP, Q ∈ PROP] then ¬(P ∧ Q);
	apply not_intro;
	if PQ: P ∧ Q then false;
		by not_imp_false[OF nQ] and_elim2[OF PQ].
	.

lemma nand_iff_imp_not: if [P ∈ PROP, Q ∈ PROP] then ¬(P ∧ Q) ⟺ (P ⟹ ¬Q);
	unfold+ not_iff_imp_false and_imp_iff.

lemma non_contradiction: if [P ∈ PROP] then ¬(P ∧ ¬P);
	unfold nand_iff_imp_not;
	by nnot_intro.

lemma nand_nnot_iff: if [P ∈ PROP, Q ∈ PROP] then ¬(P ∧ ¬¬Q) ⟺ ¬(P ∧ Q);
	unfold+ nand_iff_imp_not;
	unfold nnnot_iff.

lemma nnot_nand_iff: if [P ∈ PROP, Q ∈ PROP] then ¬(¬¬P ∧ Q) ⟺ ¬(P ∧ Q);
	unfold and_iff.commute;
	unfold nand_nnot_iff;
	unfold and_iff.commute.

---
### Disjunction
---

lemma or_iff_true1: if !P, !P ∈ PROP, !Q ∈ PROP then P ∨ Q ⟺ true;
	by iff_intro or_intro1.

lemma or_iff_true2: if !Q, !P ∈ PROP, !Q ∈ PROP then P ∨ Q ⟺ true;
	by iff_intro or_intro2.

lemma or_intro:
	if PQR: ∀R. R ∈ PROP ⟹ (P ⟹ R) ⟹ (Q ⟹ R) ⟹ R, ! P ∈ PROP, ! Q ∈ PROP
	then P ∨ Q;
	apply PQR;
	by #unfold or_iff_true1 or_iff_true2.

interpret or: Relation prop (∨).

interpret or: Symmetric prop (∨);
	by #elim or_elim #unfold or_iff_true1 or_iff_true2.

lemma iff_cong_or#cong: for P Q
	if PP': P ⟺ P', QQ': Q ⟺ Q', [P ∈ PROP, Q ∈ PROP, P' ∈ PROP, Q' ∈ PROP]
	then P ∨ Q ⟺ P' ∨ Q';
	by iff_intro #elim or_elim #unfold PP' QQ' or_iff_true1 or_iff_true2.

interpret or: Magma prop (∨).

interpret or_iff: Commutative prop (∨) (⟺);
	by iff_intro #elim or_elim #unfold or_iff_true1 or_iff_true2.

interpret or_iff: Associative prop (∨) (⟺);
	by iff_intro #elim or_elim #unfold or_iff_true1 or_iff_true2.

lemma false_or_false_iff: false ∨ false ⟺ false;
	by iff_intro or_intro1 #elim or_elim.

lemma true_or: if [P ∈ PROP] then true ∨ P;
	by or_intro1.

lemma or_true: if [P ∈ PROP] then P ∨ true;
	by or_intro2.

lemma or_imp_iff:
	if [P ∈ PROP, Q ∈ PROP, R ∈ PROP]
	then (P ∨ Q ⟹ R) ⟺ (P ⟹ R) ∧ (Q ⟹ R);
	apply iff_intro;
	if nor: P ∨ Q ⟹ R;
		by and_intro nor or_intro.
	- by #elim or_elim and_elim.
	.

lemma nor_iff: if [P ∈ PROP, Q ∈ PROP] then ¬(P ∨ Q) ⟺ ¬P ∧ ¬Q;
	unfold+ not_iff_imp_false;
	by or_imp_iff.

lemma nnot_nor_iff: if [P ∈ PROP, Q ∈ PROP] then ¬(¬¬P ∨ Q) ⟺ ¬(P ∨ Q);
	unfold+ nor_iff nnnot_iff.

lemma nor_nnot_iff: if [P ∈ PROP, Q ∈ PROP] then ¬(P ∨ ¬¬Q) ⟺ ¬(P ∨ Q);
	unfold+ nor_iff nnnot_iff.

lemma nnot_excluded_middle: if [P ∈ PROP] then ¬¬(P ∨ ¬P);
	unfold nor_iff;
	by non_contradiction.

lemma or_imp_nand: if PQ: P ∨ Q, [P ∈ PROP, Q ∈ PROP] then ¬(¬P ∧ ¬Q);
	apply not_intro;
	apply or_elim[OF PQ];
	- by not_imp_false[of P] #elim and_elim.
	- by not_imp_false[of Q] #elim and_elim.
	.


lemma nnand_iff: if [P ∈ PROP, Q ∈ PROP] then ¬¬(P ∧ Q) ⟺ ¬¬P ∧ ¬¬Q;
	fold nnot_nand_iff;
	fold nand_nnot_iff;
	fold nor_iff;
	unfold nnnot_iff.

lemma nniff_iff: if [P ∈ PROP, Q ∈ PROP] then ¬¬(¬P ⟺ ¬Q) ⟺ ¬P ⟺ ¬Q;
	unfold[0]+ iff_iff_and nnand_iff nnimp_not_iff;
	fold[0] iff_iff_and.

