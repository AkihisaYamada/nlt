-------
# Type-Free Minimal Logic
-------
fix true false (¬) (∧) (⟺) (∨) (∃).

assume true_intro! true.

assume iff_intro: if P ⟹ Q, Q ⟹ P then P ⟺ Q.
assume iff_elim1: if P ⟺ Q, P then Q.
assume iff_elim2: if P ⟺ Q, Q then P.

assume and_intro! if P, Q then P ∧ Q.
assume and_elim1: if P ∧ Q then P.
assume and_elim2: if P ∧ Q then Q.

assume not_imp_false: if ¬P, P then false.
assume not_intro: if P ⟹ false then ¬P.

assume or_intro1: for P Q if P then P ∨ Q.
assume or_intro2: for P Q if Q then P ∨ Q.
assume or_elim: if P ∨ Q then for R if P ⟹ R, Q ⟹ R then R.

assume ex_intro1: for x if P.[x] then ∃x. P.[x].
assume ex_elim: if ∃x. P.[x] then for Q if ∀x. P.[x] ⟹ Q then Q.

begin
---
## Theorems
---

---
### If-and-only-if
---

lemma iff_elim: if PQ: P ⟺ Q then for R if imp: (P ⟹ Q) ⟹ (Q ⟹ P) ⟹ R then R;
	by imp iff_elim1[OF PQ] iff_elim2[OF PQ].

namespace iff:

	-- We can think of meta-magmas with respect to ⟺
	interpret MetaMagmas (⟺).

	interpret MetaEquivalence (⟺);
		-; by iff_intro.
		-; by iff_intro #elim iff_elim.
		- for P Q R if PQ: P ⟺ Q, QR: Q ⟺ R then P ⟺ R;
			apply iff_intro;
			-; by iff_elim1[OF QR] iff_elim1[OF PQ].
			-; by iff_elim2[OF PQ] iff_elim2[OF QR].
			.
		.
	--

end

note! iff.refl.

set rewrite iff_elim1 iff_elim2 iff.refl iff.trans.
set dual iff.sym.

context iff begin

	interpret MetaCompatible (⟺);
		- for P R Q S if PQ: P ⟺ Q, RS: R ⟺ S then (P ⟺ R) ⟺ (Q ⟺ S);
			apply iff_intro;
			- if PR: P ⟺ R then Q ⟺ S;
				have QR: Q ⟺ R;
					by iff.trans[OF iff.sym[OF PQ] PR].
				by iff.trans[OF QR RS].
			- if QS: Q ⟺ S then P ⟺ R;
				have PS: P ⟺ S;
					by iff.trans[OF PQ QS].
				by iff.trans[OF PS iff.sym[OF RS]].
			.
		.

	namespace imp:
		interpret MetaCompatible (⟹);
			- for P R Q S if PQ: P ⟺ Q, RS: R ⟺ S then (P ⟹ R) ⟺ (Q ⟹ S);
				apply iff_intro;
				- if PR: P ⟹ R, !Q then S;
					by iff_elim1[OF RS] PR iff_elim2[OF PQ].
				- if QS: Q ⟹ S, !P then R;
					by iff_elim2[OF RS] QS iff_elim1[OF PQ].
				.
			.
	end

	lemma all_cong: if PQ: ∀x. P.[x] ⟺ Q.[x] then (∀x. P.[x]) ⟺ (∀x. Q.[x]);
		apply iff_intro;
		- if ! ∀x. P.[x] then ∀x. Q.[x];
			by iff_elim1[OF PQ].
		- if ! ∀x. Q.[x] then ∀x. P.[x];
			by iff_elim2[OF PQ].
		.

end

note(cong) iff.cong iff.imp.cong iff.all_cong.

lemma imp_imp_iff: if !P then (P ⟹ Q) ⟺ Q;
	by iff_intro.

lemma imp_iff_iff: if !P then (P ⟺ Q) ⟺ Q;
	by iff_intro #elim iff_elim.

lemma all_imp2_iff: (∀Q. (P ⟹ Q) ⟹ Q) ⟺ P;
	by iff_intro.

lemma imp3_iff: (((P ⟹ Q) ⟹ Q) ⟹ Q) ⟺ (P ⟹ Q);
	apply iff_intro[OF imp2_imp_imp];
	- if PQ: P ⟹ Q, PQQ: (P ⟹ Q) ⟹ Q then Q;
		by PQQ[OF PQ].
	.

lemma imp_all_iff: (P ⟹ ∀x. α.[x]) ⟺ (∀x. P ⟹ α.[x]);
	apply iff_intro;
	-; by imp_all=.
	-; by all_imp=.
	.

lemma imp_iff_iff1: if [P] then (P ⟺ Q) ⟺ Q;
	by iff_intro #elim iff_elim.

lemma iff_true: P ⟹ P ⟺ true;
	by iff_intro.

lemma true_imp_iff: (true ⟹ P) ⟺ P;
	by imp_imp_iff.

lemma imp_true_iff: (P ⟹ true) ⟺ true;
	by iff_intro.

lemma true_iff_iff: (true ⟺ P) ⟺ P;
	by iff_intro #elim iff_elim.

lemma iff_true_iff: (P ⟺ true) ⟺ P;
	by iff_intro #elim iff_elim.

lemma imp_refl_iff: (P ⟹ P) ⟺ true;
	unfold iff_true_iff.

---
### Negation
---

lemma imp_not: if [P], nQ: ¬Q then ¬(P ⟹ Q);
	apply not_intro;
	- if PQ: P ⟹ Q;
		by not_imp_false[OF nQ] PQ.
	.

lemma imp_not_imp: if PQ: P ⟹ Q, nQ: ¬Q then ¬P;
	apply not_intro;
	by not_imp_false[OF nQ] PQ.

lemma imp_not_sym: if PnQ: P ⟹ ¬Q, [Q] then ¬P;
	apply not_intro;
	- if !P;
		have nQ: ¬Q;
			by PnQ.
		by not_imp_false[OF nQ].
	.

lemma nnot_intro: if [P] then ¬¬P;
	apply not_intro;
	- if nP: ¬P;
		by not_imp_false[OF nP].
	.

lemma not_imp_not_all: if nax: ¬α.[x] then ¬(∀y. α.[y]);
	by not_intro not_imp_false[OF nax].

lemma not_false: ¬false;
	by not_intro[OF imp.refl].

context iff begin
	lemma not_cong: if PQ: P ⟺ Q then ¬P ⟺ ¬Q;
		apply iff_intro;
		- if nP: ¬P;
			apply not_intro;
			by not_imp_false[OF nP] iff_elim2[OF PQ].
		- if nQ: ¬Q;
			apply not_intro;
			by not_imp_false[OF nQ] iff_elim1[OF PQ].
		.
end

note(cong) iff.not_cong.

lemma not_iff_imp_false: ¬P ⟺ (P ⟹ false);
	by iff_intro[OF not_imp_false not_intro].

lemma imp_not_commute: (P ⟹ ¬Q) ⟺ (Q ⟹ ¬P);
	by iff_intro[OF imp_not_sym imp_not_sym].

lemma nnnot_iff: ¬¬¬P ⟺ ¬P;
	unfold not_iff_imp_false;
	by imp3_iff.

lemma nnot_imp_not_iff: (¬¬P ⟹ ¬Q) ⟺ (P ⟹ ¬Q);
	unfold^1 imp_not_commute;
	unfold nnnot_iff.

lemma nnimp_imp_nnot: if nnPQ: ¬¬(P ⟹ Q), [P] then ¬¬Q;
	apply not_intro;
	- if nQ: ¬Q;
		apply+ not_imp_false[OF nnPQ] not_intro;
		- if PQ: P ⟹ Q;
			by not_imp_false[OF nQ] PQ.
		.
	.

lemma nnimp_not_iff: ¬¬(P ⟹ ¬Q) ⟺ (P ⟹ ¬Q);
	apply iff_intro;
	- if nnimp: ¬¬(P ⟹ ¬Q), P: P then ¬Q;
		by nnimp_imp_nnot[OF nnimp P, unfolded nnnot_iff].
	apply nnot_intro=.

lemma nnot_imp: if imp: ¬¬P ⟹ Q then P ⟹ Q;
	by imp nnot_intro.

lemma nnot_imp_nnot: if nnP: ¬¬P, PQ: P ⟹ Q then ¬¬Q;
	apply not_intro;
	- if !¬Q;
		have! ¬P;
			by imp_not_imp[OF PQ].
		by not_imp_false[OF nnP].
	.

lemma nnot_not_imp_nimp: if nnP: ¬¬P, [¬Q] then ¬(P ⟹ Q);
	apply not_intro;
	- if PQ: P ⟹ Q;
		have nnQ: ¬¬Q;
			by nnot_imp_nnot[OF nnP PQ].
		by not_imp_false[OF nnQ].
	.

lemma not_true_iff: ¬true ⟺ false;
	apply iff_intro;
	- if nt: ¬true;
		by not_imp_false[OF nt].
	by not_intro.

lemma not_false_iff: ¬false ⟺ true;
	by iff_true[OF not_false].

lemma false_imp_false_iff: (false ⟹ false) ⟺ true;
	by iff_true[OF imp.refl].

---
### Conjunction
---

lemma and_elim(elim) if PQ: P ∧ Q then for R if PQR: P ⟹ Q ⟹ R then R;
	by PQR and_elim1[OF PQ] and_elim2[OF PQ].

interpret and: MetaPartialEquivalence (∧).

lemma and_iff: P ∧ Q ⟺ (∀R. (P ⟹ Q ⟹ R) ⟹ R);
	by iff_intro.

context iff begin

	namespace and:
		interpret MetaCompatible (∧);
			- for P R Q S if PQ: P ⟺ Q, RS: R ⟺ S then P ∧ R ⟺ Q ∧ S;
				by iff_intro #unfold PQ RS.
			.
		interpret MetaCommMonoid (∧) true;
			by iff_intro.
	end

end

note(cong) iff.and.cong.

lemma and_imp_iff_imp_imp: (P ∧ Q ⟹ R) ⟺ (P ⟹ Q ⟹ R);
	by iff_intro.

lemma true_and_true: true ∧ true;
	.

lemma false_and_false_iff: false ∧ false ⟺ false;
	by iff_intro.

lemma iff_iff_and: (P ⟺ Q) ⟺ (P ⟹ Q) ∧ (Q ⟹ P);
	by iff_intro #elim iff_elim.

lemma all_and_iff: (∀x. P.[x] ∧ Q.[x]) ⟺ (∀x. P.[x]) ∧ (∀x. Q.[x]);
	apply iff_intro;
	- if ab: ∀x. P.[x] ∧ Q.[x];
		apply and_intro;
		- for x;
			by and_elim1[OF ab].
		- for x;
			by and_elim2[OF ab].
		.
	unfold and_imp_iff_imp_imp;
	- if ! ∀x. P.[x], ! ∀x. Q.[x].
	.

lemma nand_intro1: if nP: ¬P then ¬(P ∧ Q);
	by not_intro not_imp_false[OF nP].

lemma nand_intro2: if nQ: ¬Q then ¬(P ∧ Q);
	by not_intro not_imp_false[OF nQ].

lemma nand_iff_imp_not: ¬(P ∧ Q) ⟺ (P ⟹ ¬Q);
	unfold not_iff_imp_false and_imp_iff_imp_imp.

lemma non_contradiction: ¬(P ∧ ¬P);
	unfold nand_iff_imp_not;
	by nnot_intro.

lemma nand_nnot_iff: ¬(P ∧ ¬¬Q) ⟺ ¬(P ∧ Q);
	unfold nand_iff_imp_not nnnot_iff.

lemma nnot_nand_iff: ¬(¬¬P ∧ Q) ⟺ ¬(P ∧ Q);
	unfold^1 iff.and.commute;
	unfold nand_nnot_iff;
	unfold^1 iff.and.commute.

lemma raw_or_imp_iff: ((∀S. (P ⟹ S) ⟹ (Q ⟹ S) ⟹ S) ⟹ R) ⟺ (P ⟹ R) ∧ (Q ⟹ R);
	apply iff_intro;
	- if or_imp;
		by or_imp.
	- if and: (P ⟹ R) ∧ (Q ⟹ R), or: (∀S. (P ⟹ S) ⟹ (Q ⟹ S) ⟹ S);
		by or[OF and_elim1[OF and] and_elim2[OF and]].
	.

lemma raw_nor_iff_and: ¬(∀R. (P ⟹ R) ⟹ (Q ⟹ R) ⟹ R) ⟺ ¬P ∧ ¬Q;
	unfold not_iff_imp_false;
	by raw_or_imp_iff.

lemma nnand_iff: ¬¬(P ∧ Q) ⟺ ¬¬P ∧ ¬¬Q;
	fold^1 nnot_nand_iff;
	fold^1 nand_nnot_iff;
	fold raw_nor_iff_and;
	unfold nnnot_iff;
	unfold raw_nor_iff_and.

---
### Disjunction
---

lemma or_intro: if assm: ∀R. (P ⟹ R) ⟹ (Q ⟹ R) ⟹ R then P ∨ Q;
	by assm[OF or_intro1 or_intro2].

namespace or:
	interpret MetaSymmetric (∨);
		by or_intro #elim or_elim.
end

lemma or_iff_true1: if ! P then P ∨ Q ⟺ true;
	by iff_intro or_intro1.

lemma or_iff_true2: if ! Q then P ∨ Q ⟺ true;
	by iff_intro or_intro2.

context iff begin
	namespace or:
		interpret MetaCompatible (∨);
			- for P R Q S if PQ: P ⟺ Q, RS: R ⟺ S then P ∨ R ⟺ Q ∨ S;
				by iff_intro or_intro #elim or_elim #unfold PQ RS.
			.
		interpret MetaCommAbsorb (∨) true;
			-; by iff_intro or_intro.
			-; by iff_intro[OF or.sym or.sym].
			.
		interpret MetaAssociative (∨);
			by iff_intro #elim or_elim #unfold or_iff_true1 or_iff_true2.
	end
end

note(cong) iff.or.cong.

lemma imp_or_if: if or: (P ⟹ Q) ∨ (P ⟹ R), [P] then Q ∨ R;
	by or[unfolded imp_imp_iff].

lemma or_imp_iff: (P ∨ Q ⟹ R) ⟺ (P ⟹ R) ∧ (Q ⟹ R);
	apply iff_intro;
	- if !;
		by or_intro.
	by #elim or_elim.

lemma nor_iff: ¬(P ∨ Q) ⟺ ¬P ∧ ¬Q;
	unfold not_iff_imp_false;
	by or_imp_iff.

lemma nnot_nor_iff: ¬(¬¬P ∨ Q) ⟺ ¬(P ∨ Q);
	unfold nor_iff nnnot_iff.

lemma nor_nnot_iff: ¬(P ∨ ¬¬Q) ⟺ ¬(P ∨ Q);
	unfold nor_iff nnnot_iff.

lemma nnot_excluded_middle: ¬¬(P ∨ ¬P);
	unfold nor_iff;
	by non_contradiction.

lemma or_imp_nand: if PQ: P ∨ Q then ¬(¬P ∧ ¬Q);
	apply not_intro;
	- if and: ¬P ∧ ¬Q;
		have nP: ¬P;
			by and_elim1[OF and].
		have nQ: ¬Q;
			by and_elim2[OF and].
		apply or_elim[OF PQ];
		-; by not_imp_false[OF nP].
		-; by not_imp_false[OF nQ].
		.
	.

lemma false_or_false_iff: false ∨ false ⟺ false;
	by iff_intro or_intro #elim or_elim.


---
### Existence
---
lemma ex_intro: if assm: ∀Q. (∀x. P.[x] ⟹ Q) ⟹ Q then ∃x. P.[x];
	apply assm;
	- for x;
		apply ex_intro1=.
	.
lemma ex_imp_all_imp: if ex: ∃x. P.[x] ⟹ Q, [∀x. P.[x]] then Q;
	apply ex_elim[OF ex];
	- for x if imp: P.[x] ⟹ Q;
		by imp.
	.
lemma ex_iff: (∃x. P.[x]) ⟺ (∀Q. (∀x. P.[x] ⟹ Q) ⟹ Q);
	apply iff_intro;
	-; apply ex.elim=.
	apply ex.intro=.

lemma all_imp_iff_ex: (∀x. P.[x] ⟹ Q) ⟺ (∃x. P.[x]) ⟹ Q;
	apply iff_intro;
	- if imp: ∀x. P.[x] ⟹ Q, ex: ∃x. P.[x];
		obtain x where Px: P.[x];
			- for thesis;
				apply ex[unfolded ex_iff, of thesis]=.
			.
		by imp[OF Px].
	- if imp: (∃x. P.[x]) ⟹ Q;
		- for x if Px: P.[x];
			by imp ex_intro1[OF Px].
		.
	.

lemma nex_iff_all_not: ¬(∃x. P.[x]) ⟺ (∀x. ¬P.[x]);
	unfold not_iff_imp_false;
	fold all_imp_iff_ex.


---
### Double negation and universal quantification.

The following direction is provable in general, but the opposite direction requires something similar to the axiom of choice.
---
lemma nnall_imp: if nnall: ¬¬(∀x. P.[x]) then ∀x. ¬¬P.[x];
	- for x;
		apply not_intro;
		- if nPx: ¬P.[x];
			by not_imp_false[OF nnall] not_imp_not_all[OF nPx].
		.
	.

---
The other direction is provable if inside the quantification has negation.
---

lemma nnall_not_iff: ¬¬(∀x. ¬P.[x]) ⟺ (∀x. ¬P.[x]);
	fold nex_iff_all_not;
	by nnnot_iff.

---
## Theories

The logical operators allow us to define some properties.
---

theory MetaIrreflexive:
	fix (<).
	assume irrefl: ¬ x < x.
end

theory MetaAsymmetric:
	fix (<).
	assume asym: x < y ⟹ ¬ y < x.
end
---
Note that antisymmetry is not yet definable, because it requires equality.
---
theory MetaOrder:
	import MetaIrreflexive.
	import MetaTransitive (<).
begin
	interpret MetaAsymmetric;
		- for x y if xy: x < y then ¬ y < x;
			apply not_intro;
			- if yx: y < x;
				have xx: x < x;
					by trans[OF xy yx].
				by not_imp_false[OF irrefl xx].
			.
		.
end

theory Membership:
	import ..Membership.
	fix (∀∈) (∃∈).
	assume ball_iff: (∀x ∈ A. P.[x]) ⟺ (∀x. x ∈ A ⟹ P.[x]).
	assume bex_iff: (∃x ∈ A. P.[x]) ⟺ (∃x. x ∈ A ∧ P.[x]).
begin
	lemma ball_intro: if all: ∀x. x ∈ A ⟹ P.[x] then ∀x ∈ A. P.[x];
		by all[folded ball_iff].
	lemma ball_elim1: if ball: ∀x ∈ A. P.[x], x: x ∈ A then P.[x];
		by ball[unfolded ball_iff, OF x].
	lemma ball_elim: if ball: ∀x ∈ A. P.[x], imp: (∀x. x ∈ A ⟹ P.[x]) ⟹ Q then Q;
		by imp ball[unfolded ball_iff].
	lemma bex_intro1: for x if x: x ∈ A, Px: P.[x] then ∃x ∈ A. P.[x];
		unfold bex_iff;
		by x Px.
	lemma bex_intro: if imp: (∀x. x ∈ A ⟹ P.[x] ⟹ Q) ⟹ Q then ∃x ∈ A. P.[x];
		apply imp;
		- for x;
			by bex_intro[of x].
		.
	lemma bex_elim: if bex: ∃x ∈ A. P.[x] then for Q if all: ∀x. x ∈ A ⟹ P.[x] ⟹ Q then Q;
		apply bex[unfolded bex_iff, THEN ex_elim];
		- for x;
			by all[of x].
		.
	theory Irreflexive:
		fix A (<).
		assume irrefl: if x ∈ A then ¬ x < x.
	end
	theory Asymmetric:
		fix A (<).
		assume asym: if x < y, x ∈ A, y ∈ A then ¬ y < x.
	end
	theory StrictOrder:
		import Irreflexive.
		import Transitive A (<).
	begin
		interpret Asymmetric;
			- for x y if xy: x < y, x! x ∈ A, !y ∈ A then ¬ y < x;
				apply not_intro;
				- if yx: y < x;
					have xx: x < x;
						by trans[OF xy yx].
					by not_imp_false[OF irrefl[OF x] xx].
				.
			.
	end
	theory Connex:
		fix A (≤).
		assume comparable: if x ∈ A, y ∈ A then x ≤ y ∨ y ≤ x.
	begin
		interpret Reflexive;
			- for x if x! x ∈ A then x ≤ x;
				apply or_elim[OF comparable[OF x x]].
			.
	end
	theory TotalPreorder:
		import Connex.
		import Transitive.
	begin
		interpret Preorder.
	end
end

theory Propositional:
	fix Prop.
	import Classes.
	import true: Member true Prop.
	import false: Member false Prop.
	import imp: Magma Prop (⟹).
	import iff: Magma Prop (⟺).
	import and: Magma Prop (∧).
	import or: Magma Prop (∨).
begin

end

theory FirstOrder:
	fix QTYPE.
	import Propositional.
	assume ball_prop: if A ∈ QTYPE, ∀x. x ∈ A ⟹ P.[x] ∈ Prop then (∀x ∈ A. P.[x]) ∈ Prop.
	import bex_prop: if A ∈ QTYPE, ∀x. x ∈ A ⟹ P.[x] ∈ Prop then (∃x ∈ A. P.[x]) ∈ Prop.
begin
	theory Impredicative:
		assume Prop_type: Prop ∈ QTYPE.
	end
end

theory SecondOrder:
	fix IND.
	import FirstOrder.
	assume IND_type: if A ∈ IND then A ∈ QTYPE.
	assume IND_Fun_type: if A ∈ IND, B ∈ QTYPE then A → B ∈ QTYPE.
begin
	theory Impredicative:
		import Impredicative.
	end
end

theory HigherOrder:
	import FirstOrder.
	assume fun_type: if A ∈ QTYPE, B ∈ QTYPE then A → B ∈ QTYPE.
begin
	theory Impredicative:
		import Impredicative.
	end
end

