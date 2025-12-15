---
# Minimal Propositional Logic
---

---
## Axiomatization
---

fix false (¬) (∧) (∨) (⟺).

assume false_type! false ∈ Prop.
assume not_type! P ∈ Prop ⟹ (¬ P) ∈ Prop.
assume and_type! P ∈ Prop ⟹ Q ∈ Prop ⟹ (P ∧ Q) ∈ Prop.
assume  or_type! P ∈ Prop ⟹ Q ∈ Prop ⟹ (P ∨ Q) ∈ Prop.
assume iff_type! P ∈ Prop ⟹ Q ∈ Prop ⟹ (P ⟺ Q) ∈ Prop.

assume not_intro: (P ⟹ false) ⟹ P ∈ Prop ⟹ ¬P.
assume not_imp_false: ¬P ⟹ P ⟹ P ∈ Prop ⟹ false.
assume and_intro: P ⟹ Q ⟹ P ∈ Prop ⟹ Q ∈ Prop ⟹ P ∧ Q.
assume and_elim1: P ∧ Q ⟹ P ∈ Prop ⟹ Q ∈ Prop ⟹ P.
assume and_elim2: P ∧ Q ⟹ P ∈ Prop ⟹ Q ∈ Prop ⟹ Q.
assume or_intro1: P ⟹ P ∈ Prop ⟹ Q ∈ Prop ⟹ P ∨ Q.
assume or_intro2: ∀ P Q. Q ⟹ P ∈ Prop ⟹ Q ∈ Prop ⟹ P ∨ Q.
assume or_elim: P ∨ Q ⟹ ∀R. (P ⟹ R) ⟹ (Q ⟹ R) ⟹ P ∈ Prop ⟹ Q ∈ Prop ⟹ R ∈ Prop ⟹ R.

assume iff_intro: (P ⟹ Q) ⟹ (Q ⟹ P) ⟹ P ∈ Prop ⟹ Q ∈ Prop ⟹ (P ⟺ Q).
assume iff_elim1: (P ⟺ Q) ⟹ P ⟹ P ∈ Prop ⟹ Q ∈ Prop ⟹ Q.
assume iff_elim2: (P ⟺ Q) ⟹ Q ⟹ P ∈ Prop ⟹ Q ∈ Prop ⟹ P.

begin
---
## Theorems
---

interpret imp: Magma Prop (⟹).

namespace iff begin

	interpret Relation Prop (⟺).
	interpret Magma Prop (⟺).
	interpret Magmas (⟺).

	lemma elim:
	if PQ: P ⟺ Q then ∀R. ((P ⟹ Q) ⟹ (Q ⟹ P) ⟹ R) ⟹ P ∈ Prop ⟹ Q ∈ Prop ⟹ R;
		for R if assm, !, !;
			apply assm;
			- by iff_elim1[OF PQ].
			- by iff_elim2[OF PQ].
			.
		.

	interpret Equivalence Prop (⟺);
		- by iff_intro.
		- by iff_intro #elim elim.
		for P Q R if PQ: P ⟺ Q, QR: Q ⟺ R, !P ∈ Prop, !Q ∈ Prop, !R ∈ Prop then P ⟺ R;
			apply iff_intro;
			- by iff_elim1[OF QR] iff_elim1[OF PQ].
			by iff_elim2[OF PQ] iff_elim2[OF QR].
		by iff_intro #elim elim.

	note! refl.

	lemma imp: if PQ: P ⟺ Q, [P ∈ Prop, Q ∈ Prop] then P ⟹ Q;
		by iff_elim1[OF PQ].

	lemma imp_rev: if PQ: P ⟺ Q, [P ∈ Prop, Q ∈ Prop] then Q ⟹ P;
		by iff_elim2[OF PQ].

	set rewrite imp imp_rev refl trans.
	set dual sym.

	lemma imp_cong: for P Q
		if PP': P ⟺ P', QQ': P' ⟹ Q ⟺ Q', [P ∈ Prop, P' ∈ Prop, Q ∈ Prop, Q' ∈ Prop]
		then (P ⟹ Q) ⟺ (P' ⟹ Q');
		apply iff_intro;
		- by #unfold QQ'[dual] PP'.
		- by #unfold QQ' PP'.
		.

	interpret imp: Compatible Prop (⟹);
		for P Q P' Q' if PP': P ⟺ P', QQ': Q ⟺ Q', !P ∈ Prop, !Q ∈ Prop, !P' ∈ Prop, !Q' ∈ Prop
		then (P ⟹ Q) ⟺ (P' ⟹ Q');
			apply iff_intro;
			- by #unfold QQ'[dual] PP'.
			- by #unfold QQ' PP'.
			.
		.

	interpret Compatible Prop (⟺);
		for P Q P' Q' if PP': P ⟺ P', QQ': Q ⟺ Q', !P ∈ Prop, !Q ∈ Prop, !P' ∈ Prop, !Q' ∈ Prop
		then (P ⟺ Q) ⟺ (P' ⟺ Q');
			apply iff_intro;
			if PQ: P ⟺ Q;
				apply iff_intro;
				- by #unfold QQ'[dual] PQ[dual] PP'.
				- by #unfold PP'[dual] PQ QQ'.
				.
			if P'Q': P' ⟺ Q';
				apply iff_intro;
				- by #unfold QQ' P'Q'[dual] PP'[dual].
				- by #unfold PP' P'Q' QQ'[dual].
				.
			.
		.

end

note ! iff.refl.

set rewrite iff.imp iff.imp_rev iff.refl iff.trans.
set dual iff.sym.

note #cong: iff.cong.
note #cong: iff.imp.cong.

lemma imp_imp_iff: if [P, P ∈ Prop, Q ∈ Prop] then (P ⟹ Q) ⟺ Q;
	by iff_intro.

lemma imp_iff_iff: if [P, P ∈ Prop, Q ∈ Prop] then (P ⟺ Q) ⟺ Q;
	by iff_intro #elim iff_elim1.

lemma imp3_iff: if [P ∈ Prop, Q ∈ Prop] then (((P ⟹ Q) ⟹ Q) ⟹ Q) ⟺ (P ⟹ Q);
	apply iff_intro[OF imp2_imp_imp];
	if PQ: P ⟹ Q, PQQ: (P ⟹ Q) ⟹ Q then Q;
		by PQQ[OF PQ].
	.

----
### True, False, and Negation
----

obtain true where true_type! true ∈ Prop, true_intro! true;
	for thesis if assm;
		apply assm[of (false ⟹ false)].
	.

lemma iff_true: if [P, P ∈ Prop] then P ⟺ true;
	by iff_intro.

set to_true iff_true.

lemma not_false: ¬false;
	apply not_intro.

lemma true_imp_iff: if [P ∈ Prop] then (true ⟹ P) ⟺ P;
	by imp_imp_iff.

lemma imp_true_iff: if [P ∈ Prop] then (P ⟹ true) ⟺ true;
	by iff_intro.

lemma iff_cong_not#cong: if PP': P ⟺ P', [P ∈ Prop, P' ∈ Prop] then ¬P ⟺ ¬P';
	apply iff_intro;
	if nP: ¬P;
		apply not_intro;
		by not_imp_false[OF nP] iff_elim2[OF PP'].
	if nP': ¬P';
		apply not_intro;
		by not_imp_false[OF nP'] iff_elim1[OF PP'].
	.

lemma not_iff_imp_false: if [P ∈ Prop] then ¬P ⟺ (P ⟹ false);
	apply iff_intro;
	if nP: ¬P;
		by not_imp_false[OF nP].
	if Pf: P ⟹ false;
		by not_intro Pf.
	.

lemma not_true_iff: ¬true ⟺ false;
	unfold not_iff_imp_false true_imp_iff.

lemma nnot_intro: if P: P, [P ∈ Prop] then ¬¬P;
	unfold P not_true_iff not_false.

lemma nnot_imp: if imp: ¬¬P ⟹ Q, [P, P ∈ Prop] then Q;
	by imp nnot_intro.

lemma imp_not: if P: P, [¬Q, P ∈ Prop, Q ∈ Prop] then ¬(P ⟹ Q);
	unfold P true_imp_iff.

lemma imp_not_imp: if PQ: P ⟹ Q, nQ: ¬Q, [P ∈ Prop, Q ∈ Prop] then ¬P;
	apply not_intro;
	by not_imp_false[OF nQ] PQ.

lemma imp_not_sym: if PnQ: P ⟹ ¬Q, Q: Q, [P ∈ Prop, Q ∈ Prop] then ¬P;
	by not_intro PnQ[unfolded Q not_true_iff].

lemma nnot_imp_nnot: if nnP: ¬¬P, PQ: P ⟹ Q, [P ∈ Prop, Q ∈ Prop] then ¬¬Q;
	apply not_intro;
	if nQ: ¬Q;
		have nP: ¬P;
			by imp_not_imp[OF PQ nQ].
		by not_imp_false[OF nnP] nP.
	.

lemma nnimp_imp_nnot: if nnPQ: ¬¬(P ⟹ Q), P: P, [P ∈ Prop, Q ∈ Prop] then ¬¬Q;
	by nnPQ[unfolded P true_imp_iff].

lemma nnot_not_imp_nimp: if nnP: ¬¬P, nQ: ¬Q, [P ∈ Prop, Q ∈ Prop] then ¬(P ⟹ Q);
	apply not_intro;
	if PQ: P ⟹ Q;
		have nnQ: ¬¬Q;
			by nnot_imp_nnot[OF nnP] PQ.
		by not_imp_false[OF nnQ nQ].
	.

theorem nnnot_iff: if [P ∈ Prop] then ¬¬¬P ⟺ ¬P;
	unfold not_iff_imp_false imp3_iff.

lemma imp_not_commute:
if [P ∈ Prop, Q ∈ Prop] then (P ⟹ ¬Q) ⟺ (Q ⟹ ¬P);
	by iff_intro #elim imp_not_sym.

lemma nnot_imp_not_iff:
if [P ∈ Prop, Q ∈ Prop] then (¬¬P ⟹ ¬Q) ⟺ (P ⟹ ¬Q);
	unfold^1 imp_not_commute;
	unfold nnnot_iff.

lemma nnimp_not_iff:
if [P ∈ Prop, Q ∈ Prop] then ¬¬(P ⟹ ¬Q) ⟺ (P ⟹ ¬Q);
	apply iff_intro;
	if nnimp: ¬¬(P ⟹ ¬Q), P: P then ¬Q;
		by nnimp[unfolded P true_imp_iff nnnot_iff].
	by nnot_intro.

---
### Conjunction
---

namespace and begin

	lemma elim:
	if and: P ∧ Q then ∀R. (P ⟹ Q ⟹ R) ⟹ P ∈ Prop ⟹ Q ∈ Prop ⟹ R;
		for R if PQR: P ⟹ Q ⟹ R;
			by PQR and_elim1[OF and] and_elim2[OF and].
		.

	interpret PartialEquivalence Prop (∧);
		by and_intro #elim and.elim.

	interpret Magma Prop (∧).

end

context iff begin

	namespace and begin

		interpret Compatible Prop (∧);
			for P Q P' Q' if PP': P ⟺ P', QQ': Q ⟺ Q', !P ∈ Prop, !Q ∈ Prop, !P' ∈ Prop, !Q' ∈ Prop
			then P ∧ Q ⟺ P' ∧ Q';
				apply iff_intro;
				- by and_intro #fold PP' QQ' #elim and.elim.
				- by and_intro #unfold PP' QQ' #elim and.elim.
				.
			.

		interpret CommMonoid (∧) true;
			by iff_intro and_intro #elim and.elim.

	end

	note #cong: and.cong.

end

note #cong: iff.and.cong.

lemma iff_imp_and: if PQ: P ⟺ Q, [P ∈ Prop, Q ∈ Prop] then (P ⟹ Q) ∧ (Q ⟹ P);
	by and_intro #unfold PQ.

lemma iff_iff_and: if [P ∈ Prop, Q ∈ Prop] then (P ⟺ Q) ⟺ (P ⟹ Q) ∧ (Q ⟹ P);
	by iff_intro and_intro #elim iff.elim and.elim.

lemma and_imp_iff:
if [P ∈ Prop, Q ∈ Prop, R ∈ Prop] then (P ∧ Q ⟹ R) ⟺ (P ⟹ Q ⟹ R);
	by iff_intro and_intro #elim and.elim.

lemma nand_intro1: if nP: ¬P, [P ∈ Prop, Q ∈ Prop] then ¬(P ∧ Q);
	apply not_intro;
	if PQ: P ∧ Q then false;
		by not_imp_false[OF nP] and_elim1[OF PQ].
	.

lemma nand_intro2: for P Q if nQ: ¬Q, [P ∈ Prop, Q ∈ Prop] then ¬(P ∧ Q);
	apply not_intro;
	if PQ: P ∧ Q then false;
		by not_imp_false[OF nQ] and_elim2[OF PQ].
	.

lemma nand_iff_imp_not: if [P ∈ Prop, Q ∈ Prop] then ¬(P ∧ Q) ⟺ (P ⟹ ¬Q);
	unfold not_iff_imp_false and_imp_iff.

lemma non_contradiction: if [P ∈ Prop] then ¬(P ∧ ¬P);
	unfold nand_iff_imp_not;
	by nnot_intro.

lemma nand_nnot_iff: if [P ∈ Prop, Q ∈ Prop] then ¬(P ∧ ¬¬Q) ⟺ ¬(P ∧ Q);
	unfold nand_iff_imp_not;
	unfold nnnot_iff.

lemma nnot_nand_iff: if [P ∈ Prop, Q ∈ Prop] then ¬(¬¬P ∧ Q) ⟺ ¬(P ∧ Q);
	unfold^1 iff.and.commute;
	unfold nand_nnot_iff;
	unfold^1 iff.and.commute.

---
### Disjunction
---

lemma or_iff_true1: if !P, !P ∈ Prop, !Q ∈ Prop then P ∨ Q ⟺ true;
	by iff_intro or_intro1.

lemma or_iff_true2: if !Q, !P ∈ Prop, !Q ∈ Prop then P ∨ Q ⟺ true;
	by iff_intro or_intro2.

set print.
set print blast.
lemma or_intro:
if PQR: ∀R. R ∈ Prop ⟹ (P ⟹ R) ⟹ (Q ⟹ R) ⟹ R, ! P ∈ Prop, ! Q ∈ Prop
then P ∨ Q;
	apply PQR;
	by #unfold or_iff_true1 or_iff_true2.

namespace or begin

	interpret Symmetric Prop (∨);
		by iff_intro #elim or_elim #unfold or_iff_true1 or_iff_true2.

	interpret Magma Prop (∨).

end

context iff begin

	namespace or begin
set print.
set print blast.

		interpret Compatible Prop (∨);
			for P Q P' Q' if PP': P ⟺ P', QQ': Q ⟺ Q', !P ∈ Prop, !Q ∈ Prop, !P' ∈ Prop, !Q' ∈ Prop
			then P ∨ Q ⟺ P' ∨ Q';
				by iff_intro or_intro #elim or_elim #unfold PP' QQ'.
			.

		interpret Idempotent Prop (∨);
			by iff_intro #elim or_elim #unfold or_iff_true1.

		interpret CommSemigroupAbsorb (∨) true;
			note #unfold 1: or_iff_true1 or_iff_true2.
			by iff_intro #elim or_elim.

	end

end

lemma false_or_false_iff: false ∨ false ⟺ false;
	by iff_intro or_intro1 #elim or_elim.

lemma true_or: if [P ∈ Prop] then true ∨ P;
	by or_intro1.

lemma or_true: if [P ∈ Prop] then P ∨ true;
	by or_intro2.

lemma or_imp_iff:
if [P ∈ Prop, Q ∈ Prop, R ∈ Prop] then (P ∨ Q ⟹ R) ⟺ (P ⟹ R) ∧ (Q ⟹ R);
	apply iff_intro;
	if nor: P ∨ Q ⟹ R;
		by and_intro nor or_intro.
	- by #elim or_elim and.elim.
	.

lemma nor_iff: if [P ∈ Prop, Q ∈ Prop] then ¬(P ∨ Q) ⟺ ¬P ∧ ¬Q;
	unfold not_iff_imp_false;
	by or_imp_iff.

lemma nnot_nor_iff: if [P ∈ Prop, Q ∈ Prop] then ¬(¬¬P ∨ Q) ⟺ ¬(P ∨ Q);
	unfold nor_iff nnnot_iff.

lemma nor_nnot_iff: if [P ∈ Prop, Q ∈ Prop] then ¬(P ∨ ¬¬Q) ⟺ ¬(P ∨ Q);
	unfold nor_iff nnnot_iff.

lemma nnot_excluded_middle: if [P ∈ Prop] then ¬¬(P ∨ ¬P);
	unfold nor_iff;
	by non_contradiction.

lemma or_imp_nand: if PQ: P ∨ Q, [P ∈ Prop, Q ∈ Prop] then ¬(¬P ∧ ¬Q);
	apply not_intro;
	apply or_elim[OF PQ];
	- by not_imp_false[of P] #elim and.elim.
	- by not_imp_false[of Q] #elim and.elim.
	.


lemma nnand_iff: if [P ∈ Prop, Q ∈ Prop] then ¬¬(P ∧ Q) ⟺ ¬¬P ∧ ¬¬Q;
	fold^1 nnot_nand_iff;
	fold^1 nand_nnot_iff;
	fold nor_iff;
	unfold nnnot_iff.

lemma nniff_iff: if [P ∈ Prop, Q ∈ Prop] then ¬¬(¬P ⟺ ¬Q) ⟺ ¬P ⟺ ¬Q;
	unfold[0] iff_iff_and nnand_iff nnimp_not_iff;
	fold[0] iff_iff_and.


theory Connex:
	import Relation.
	assume connex: x ∈ A ⟹ y ∈ A ⟹ x ≤ y ∨ y ≤ x.
begin

	interpret Reflexive;
		for x if x! x ∈ A then x ≤ x;
			apply or_elim[OF connex[OF x x]].
		.

end

theory Irreflexive:
	fix A (<).
	import Relation A (<).
	assume irrefl: x ∈ A ⟹ ¬ x < x.
end

theory Asymmetric:
	fix A (<).
	import Relation A (<).
	assume asym: x < y ⟹ x ∈ A ⟹ y ∈ A ⟹ ¬ y < x.
end

theory StrictOrder:
	import Irreflexive.
	import Transitive A (<).
begin

	interpret Asymmetric;
		for x y if xy: x < y, x! x ∈ A, !y ∈ A then ¬ y < x;
			apply not_intro;
			if yx: y < x;
				have xx: x < x;
					by trans[OF xy yx].
				by not_imp_false[OF irrefl[OF x] xx].
			.
		.

end
