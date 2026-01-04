---
# Minimal Propositional Logic
---

---
## Axiomatization
---

import TypeFree.
import Minimal.

namespace false:
	import Member false Prop.
end

namespace imp:
	import Magma Prop (⟹).
end

namespace not:
	import Unary (¬) Prop Prop.
end

namespace and:
	import Magma Prop (∧).
end

namespace or:
	import Magma Prop (∨).
end

namespace iff:
	import Magma Prop (⟺).
end

begin
---
## Theorems
---

note! not.closed iff.closed and.closed or.closed.


context iff begin

	interpret Relation Prop (⟺).
	interpret Magmas (⟺).

	interpret Equivalence Prop (⟺);
		-; by iff_intro.
		-; by iff_intro #elim iff_elim.
		- for P Q R if PQ: P ⟺ Q, QR: Q ⟺ R, !P ∈ Prop, !Q ∈ Prop, !R ∈ Prop then P ⟺ R;
			apply iff_intro;
			-; by iff_elim1[OF QR] iff_elim1[OF PQ].
			-; by iff_elim2[OF PQ] iff_elim2[OF QR].
			.
		by iff_intro #elim iff_elim.

end

context iff begin

	lemma imp_cong:
		for P Q if [P ∈ Prop, Q ∈ Prop] then
		for P' Q' if PP': P ⟺ P', QQ': P' ⟹ Q ⟺ Q', [P' ∈ Prop, Q' ∈ Prop]
		then (P ⟹ Q) ⟺ (P' ⟹ Q');
	apply intro;
	-; by #unfold QQ'[dual] PP'.
	-; by #unfold QQ' PP'.
	.

	interpret imp: Compatible Prop (⟹);
	- for P P' Q Q' if PP': P ⟺ P', QQ': Q ⟺ Q', !, !, !, !
	  then (P ⟹ Q) ⟺ (P' ⟹ Q');
		apply intro;
		-; by #unfold QQ'[dual] PP'.
		-; by #unfold QQ' PP'.
		.
	.

	interpret Compatible Prop (⟺);
	- for P P' Q Q' if PP': P ⟺ P', QQ': Q ⟺ Q', !, !, !, !
	  then (P ⟺ Q) ⟺ (P' ⟺ Q');
		apply intro;
		- if PQ: P ⟺ Q;
			apply intro;
			-; by #unfold QQ'[dual] PQ[dual] PP'.
			-; by #unfold PP'[dual] PQ QQ'.
			.
		- if P'Q': P' ⟺ Q';
			apply intro;
			-; by #unfold QQ' P'Q'[dual] PP'[dual].
			-; by #unfold PP' P'Q' QQ'[dual].
			.
		.
	.

end

note (cong) iff.cong iff.imp.cong.

lemma imp_imp_iff: if [P, P ∈ Prop, Q ∈ Prop] then (P ⟹ Q) ⟺ Q;
by iff.intro.

lemma imp_iff_iff: if [P, P ∈ Prop, Q ∈ Prop] then (P ⟺ Q) ⟺ Q;
by iff.intro #elim iff.elim1.

lemma imp3_iff: if [P ∈ Prop, Q ∈ Prop] then (((P ⟹ Q) ⟹ Q) ⟹ Q) ⟺ (P ⟹ Q);
apply iff.intro[OF imp2_imp_imp];
- if PQ: P ⟹ Q, PQQ: (P ⟹ Q) ⟹ Q then Q;
  by PQQ[OF PQ].
.

----
### True, False, and Negation
----

namespace true:
	obtain true where type: true ∈ Prop, intro: true;
	- for thesis if assm;
		apply assm[of (false ⟹ false)].
	.
end

note! true.type true.intro.

lemma iff_true: if [P, P ∈ Prop] then P ⟺ true;
by iff.intro.

lemma not_false: ¬false;
apply not.intro.

lemma true_imp_iff: if [P ∈ Prop] then (true ⟹ P) ⟺ P;
by imp_imp_iff.

lemma imp_true_iff: if [P ∈ Prop] then (P ⟹ true) ⟺ true;
by iff.intro.

context iff begin

	lemma cong_not: if [P ∈ Prop] then if PP': P ⟺ P', !P' ∈ Prop then ¬P ⟺ ¬P';
	apply iff.intro;
	- if nP: ¬P;
		apply not.intro;
		by not_imp_false[OF nP] iff.elim2[OF PP'].
	- if nP': ¬P';
		apply not.intro;
		by not_imp_false[OF nP'] iff.elim1[OF PP'].
	.

end

note(cong) iff.cong_not.

lemma not_iff_imp_false: if [P ∈ Prop] then ¬P ⟺ (P ⟹ false);
apply iff.intro;
- if nP: ¬P;
	by not_imp_false[OF nP].
- if Pf: P ⟹ false;
	by not.intro Pf.
.

lemma not_true_iff: ¬true ⟺ false;
unfold not_iff_imp_false true_imp_iff.

lemma nnot_intro: if P: P, [P ∈ Prop] then ¬¬P;
unfold iff_true[OF P] not_true_iff iff_true[OF not_false].

lemma nnot_imp: if imp: ¬¬P ⟹ Q, [P, P ∈ Prop] then Q;
by imp nnot_intro.

lemma imp_not: if P: P, [¬Q, P ∈ Prop, Q ∈ Prop] then ¬(P ⟹ Q);
unfold iff_true[OF P] true_imp_iff.

lemma imp_not_imp: if PQ: P ⟹ Q, nQ: ¬Q, [P ∈ Prop, Q ∈ Prop] then ¬P;
	apply not.intro;
by not_imp_false[OF nQ] PQ.

lemma imp_not_sym: if PnQ: P ⟹ ¬Q, Q: Q, [P ∈ Prop, Q ∈ Prop] then ¬P;
by not.intro PnQ[unfolded iff_true[OF Q] not_true_iff].

lemma nnot_imp_nnot: if nnP: ¬¬P, PQ: P ⟹ Q, [P ∈ Prop, Q ∈ Prop] then ¬¬Q;
apply not.intro;
- if nQ: ¬Q;
	have nP: ¬P;
		by imp_not_imp[OF PQ nQ].
	by not_imp_false[OF nnP] nP.
.

lemma nnimp_imp_nnot: if nnPQ: ¬¬(P ⟹ Q), P: P, [P ∈ Prop, Q ∈ Prop] then ¬¬Q;
by nnPQ[unfolded iff_true[OF P] true_imp_iff].

lemma nnot_not_imp_nimp: if nnP: ¬¬P, nQ: ¬Q, [P ∈ Prop, Q ∈ Prop] then ¬(P ⟹ Q);
apply not.intro;
- if PQ: P ⟹ Q;
	have nnQ: ¬¬Q;
		by nnot_imp_nnot[OF nnP] PQ.
	by not_imp_false[OF nnQ nQ].
.

theorem nnnot_iff: if [P ∈ Prop] then ¬¬¬P ⟺ ¬P;
unfold not_iff_imp_false imp3_iff.

lemma imp_not_commute:
	if [P ∈ Prop, Q ∈ Prop] then (P ⟹ ¬Q) ⟺ (Q ⟹ ¬P);
by iff.intro #elim imp_not_sym.

lemma nnot_imp_not_iff:
	if [P ∈ Prop, Q ∈ Prop] then (¬¬P ⟹ ¬Q) ⟺ (P ⟹ ¬Q);
unfold^1 imp_not_commute;
unfold nnnot_iff.

lemma nnimp_not_iff:
	if [P ∈ Prop, Q ∈ Prop] then ¬¬(P ⟹ ¬Q) ⟺ (P ⟹ ¬Q);
apply iff.intro;
- if nnimp: ¬¬(P ⟹ ¬Q), P: P then ¬Q;
	by nnimp[unfolded iff_true[OF P] true_imp_iff nnnot_iff].
by nnot_intro.

---
### Conjunction
---

context and begin

	lemma elim:
		if and: P ∧ Q then for R if PQR: (P ⟹ Q ⟹ R), ! P ∈ Prop, !Q ∈ Prop then R;
	by PQR elim1[OF and] elim2[OF and].

	interpret PartialEquivalence Prop (∧);
	by intro #elim elim.

	interpret Magma Prop (∧).

end

context iff begin

	namespace and:

		interpret Compatible Prop (∧);
		- for P P' Q Q' if PP': P ⟺ P', QQ': Q ⟺ Q', !, !, !, !
		  then P ∧ Q ⟺ P' ∧ Q';
			apply intro;
			-; by and.intro #fold PP' QQ' #elim and.elim.
			-; by and.intro #unfold PP' QQ' #elim and.elim.
			.
		.

		interpret CommMonoid (∧) true;
			by intro and.intro #elim and.elim.

	end

	note (cong) and.cong.

end

note (cong) iff.and.cong.

lemma iff_imp_and: if PQ: P ⟺ Q, [P ∈ Prop, Q ∈ Prop] then (P ⟹ Q) ∧ (Q ⟹ P);
by and.intro #unfold PQ.

lemma iff_iff_and: if [P ∈ Prop, Q ∈ Prop] then (P ⟺ Q) ⟺ (P ⟹ Q) ∧ (Q ⟹ P);
by iff.intro and.intro #elim iff.elim and.elim.

lemma and_imp_iff: if [P ∈ Prop, Q ∈ Prop, R ∈ Prop] then (P ∧ Q ⟹ R) ⟺ (P ⟹ Q ⟹ R);
by iff.intro and.intro #elim and.elim.

lemma nand_intro1: if nP: ¬P, [P ∈ Prop, Q ∈ Prop] then ¬(P ∧ Q);
apply not.intro;
- if PQ: P ∧ Q then false;
	by not_imp_false[OF nP] and.elim1[OF PQ].
.

lemma nand_intro2: for P Q if nQ: ¬Q, [P ∈ Prop, Q ∈ Prop] then ¬(P ∧ Q);
apply not.intro;
- if PQ: P ∧ Q then false;
	by not_imp_false[OF nQ] and.elim2[OF PQ].
.

lemma nand_iff_imp_not: if [P ∈ Prop, Q ∈ Prop] then ¬(P ∧ Q) ⟺ (P ⟹ ¬Q);
unfold not_iff_imp_false and_imp_iff.

lemma non_contradiction: if [P ∈ Prop] then ¬(P ∧ ¬P);
	unfold nand_iff_imp_not;
by nnot_intro.

lemma nand_nnot_iff: if [P ∈ Prop, Q ∈ Prop] then ¬(P ∧ ¬¬Q) ⟺ ¬(P ∧ Q);
	unfold nand_iff_imp_not;
	unfold nnnot_iff;
.

lemma nnot_nand_iff: if [P ∈ Prop, Q ∈ Prop] then ¬(¬¬P ∧ Q) ⟺ ¬(P ∧ Q);
	unfold^1 iff.and.commute;
	unfold nand_nnot_iff;
	unfold^1 iff.and.commute;
.

---
### Disjunction
---

lemma or_iff_true1: if !P, !P ∈ Prop, !Q ∈ Prop then P ∨ Q ⟺ true;
by iff.intro or.intro1.

lemma or_iff_true2: if !Q, !P ∈ Prop, !Q ∈ Prop then P ∨ Q ⟺ true;
by iff.intro or.intro2.

context or begin

	lemma intro:
		if PQR: ∀R. R ∈ Prop ⟹ (P ⟹ R) ⟹ (Q ⟹ R) ⟹ R, ! P ∈ Prop, ! Q ∈ Prop
		then P ∨ Q;
		apply PQR;
	by #unfold or_iff_true1 or_iff_true2.

	interpret Symmetric Prop (∨);
	by iff.intro #elim or.elim #unfold or_iff_true1 or_iff_true2.

	interpret Magma Prop (∨).

end

context iff begin

	namespace or:

		interpret Compatible Prop (∨);
		- for P P' Q Q' if PP': P ⟺ P', QQ': Q ⟺ Q', !P ∈ Prop, !Q ∈ Prop, !P' ∈ Prop, !Q' ∈ Prop
		  then P ∨ Q ⟺ P' ∨ Q';
			by intro or.intro #elim or.elim #unfold PP' QQ'.
		.

		interpret Idempotent Prop (∨);
		by intro #elim or.elim #unfold or_iff_true1.

		interpret CommSemigroupAbsorb (∨) true;
		by iff.intro #elim or.elim #unfold or_iff_true1 or_iff_true2.

	end

end

lemma false_or_false_iff: false ∨ false ⟺ false;
by iff.intro or.intro1 #elim or.elim.

lemma true_or: if [P ∈ Prop] then true ∨ P;
by or.intro1.

lemma or_true: if [P ∈ Prop] then P ∨ true;
by or.intro2.

lemma or_imp_iff:
	if [P ∈ Prop, Q ∈ Prop, R ∈ Prop] then (P ∨ Q ⟹ R) ⟺ (P ⟹ R) ∧ (Q ⟹ R);
apply iff.intro;
- if nor: P ∨ Q ⟹ R;
	by and.intro nor or.intro.
by #elim or.elim and.elim.

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
	apply not.intro;
	apply or.elim[OF PQ];
	-; by not_imp_false[of P] #elim and.elim.
	-; by not_imp_false[of Q] #elim and.elim.
	.

lemma nnand_iff: if [P ∈ Prop, Q ∈ Prop] then ¬¬(P ∧ Q) ⟺ ¬¬P ∧ ¬¬Q;
	fold^1 nnot_nand_iff;
	fold^1 nand_nnot_iff;
	fold nor_iff;
	unfold nnnot_iff;
.

lemma nniff_iff: if [P ∈ Prop, Q ∈ Prop] then ¬¬(¬P ⟺ ¬Q) ⟺ ¬P ⟺ ¬Q;
	unfold[0] iff_iff_and nnand_iff nnimp_not_iff;
	fold[0] iff_iff_and;
.
