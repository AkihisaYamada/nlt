-------
# Type-Free Minimal Logic
-------
import Base.

fix false (¬) (∧) (⟺) (∨) (∃).

assume and_intro! P ⟹ Q ⟹ P ∧ Q.
assume and_elim1: P ∧ Q ⟹ P.
assume and_elim2: P ∧ Q ⟹ Q.

assume not_imp_false: ¬ P ⟹ P ⟹ false.
assume not_intro: (P ⟹ false) ⟹ ¬ P.

assume iff_intro: (P ⟹ Q) ⟹ (Q ⟹ P) ⟹ P ⟺ Q.
assume iff_elim1: (P ⟺ Q) ⟹ P ⟹ Q.
assume iff_elim2: (P ⟺ Q) ⟹ Q ⟹ P.

assume or_intro1: P ⟹ P ∨ Q.
assume or_intro2: for P Q, Q ⟹ P ∨ Q.
assume or_elim: P ∨ Q ⟹ ∀R. (P ⟹ R) ⟹ (Q ⟹ R) ⟹ R.

assume ex_intro1: for x, α.[x] ⟹ ∃x. α.[x].
assume ex_elim: (∃x. α.[x]) ⟹ ∀P. (∀x. α.[x] ⟹ P) ⟹ P.

begin
---
## Theorems
---

-- Obtains true, which is provable.
obtain true where true_intro! true;
	for thesis if assm: ∀true. true ⟹ thesis;
		by assm[of (false ⟹ false)].
	.

---
### If-and-only-if
---

lemma iff_elim: if PQ: P ⟺ Q then ∀R. ((P ⟹ Q) ⟹ (Q ⟹ P) ⟹ R) ⟹ R;
	for R if imp;
		by imp iff_elim1[OF PQ] iff_elim2[OF PQ].
	.

namespace iff begin

	interpret MetaEquivalence (⟺);
		- by iff_intro.
		- by iff_intro #elim iff_elim.
		for P Q R if PQ: P ⟺ Q, QR: Q ⟺ R then P ⟺ R;
			apply iff_intro;
			- by iff_elim1[OF QR] iff_elim1[OF PQ].
			- by iff_elim2[OF PQ] iff_elim2[OF QR].
			.
		.
-- TODO
	note! refl.

	set rewrite iff_elim1 iff_elim2 refl trans.
	set dual sym.

	-- We can think of meta-magmas with respect to ⟺
	interpret MetaMagmas (⟺).

end

note! iff.refl.

set rewrite iff_elim1 iff_elim2 iff.refl iff.trans.
set dual iff.sym.

lemma iff_cong_imp#cong: for P R if PQ: P ⟺ Q, RS: R ⟺ S then (P ⟹ R) ⟺ (Q ⟹ S);
	apply iff_intro;
	if PR: P ⟹ R, !Q then S;
		by iff_elim1[OF RS] PR iff_elim2[OF PQ].
	if QS: Q ⟹ S, !P then R;
		by iff_elim2[OF RS] QS iff_elim1[OF PQ].
	.

lemma iff_cong_iff#cong: for P R if PQ: P ⟺ Q, RS: R ⟺ S then (P ⟺ R) ⟺ (Q ⟺ S);
	apply iff_intro;
	if PR: P ⟺ R then Q ⟺ S;
		have QR: Q ⟺ R;
			by iff.trans[OF iff.sym[OF PQ] PR].
		by iff.trans[OF QR RS].
	if QS: Q ⟺ S then P ⟺ R;
		have PS: P ⟺ S;
			by iff.trans[OF PQ QS].
		by iff.trans[OF PS iff.sym[OF RS]].
	.

lemma iff_cong_all#cong: if ab: ∀x. α.[x] ⟺ β.[x] then (∀x. α.[x]) ⟺ (∀x. β.[x]);
	apply iff_intro;
	if ! ∀x. α.[x] then ∀x. β.[x];
		by iff_elim1[OF ab].
	if ! ∀x. β.[x] then ∀x. α.[x];
		by iff_elim2[OF ab].
	.

lemma imp_imp_iff: if !P then (P ⟹ Q) ⟺ Q;
	by iff_intro.

lemma imp_iff_iff: if !P then (P ⟺ Q) ⟺ Q;
	by iff_intro #elim iff_elim.

lemma all_imp2_iff: (∀Q. (P ⟹ Q) ⟹ Q) ⟺ P;
	by iff_intro.

lemma imp3_iff: (((P ⟹ Q) ⟹ Q) ⟹ Q) ⟺ (P ⟹ Q);
	apply iff_intro[OF imp2_imp_imp];
	if PQ: P ⟹ Q, PQQ: (P ⟹ Q) ⟹ Q then Q;
		by PQQ[OF PQ].
	.

lemma imp_all_iff: (P ⟹ ∀x. α.[x]) ⟺ (∀x. P ⟹ α.[x]);
	apply iff_intro;
	- by imp_all=.
	- by all_imp=.
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
### Conjunction
---

lemma and_elim#elim: if PQ: P ∧ Q then ∀R. (P ⟹ Q ⟹ R) ⟹ R;
	for R if PQR: P ⟹ Q ⟹ R;
		by PQR and_elim1[OF PQ] and_elim2[OF PQ].
	.

interpret and: MetaPartialEquivalence (∧).

lemma and_iff: P ∧ Q ⟺ (∀R. (P ⟹ Q ⟹ R) ⟹ R);
	by iff_intro.

context iff begin

	interpret and: MetaCompatible (∧);
		for P R Q S if PQ: P ⟺ Q, RS: R ⟺ S then P ∧ R ⟺ Q ∧ S;
			by iff_intro #unfold PQ RS.
		.
	note #cong: and.cong.--TODO

	interpret and: MetaCommMonoid (∧) true;
		by iff_intro.

end

note #cong: iff.and.cong.
thm iff.and.commute.
thy.

lemma and_imp_iff: (P ∧ Q ⟹ R) ⟺ (P ⟹ Q ⟹ R);
	by iff_intro.

lemma true_and_true: true ∧ true;
	.

lemma iff_iff_and: (P ⟺ Q) ⟺ (P ⟹ Q) ∧ (Q ⟹ P);
	by iff_intro #elim iff_elim.

lemma all_and_iff: (∀x. P.[x] ∧ Q.[x]) ⟺ (∀x. P.[x]) ∧ (∀x. Q.[x]);
	apply iff_intro;
	if ab: ∀x. P.[x] ∧ Q.[x];
		apply and_intro;
		for x;
			by and_elim1[OF ab].
		for x;
			by and_elim2[OF ab].
		.
	unfold and_imp_iff;
	if ! ∀x. P.[x], ! ∀x. Q.[x].
	.

---
### Negation

Negation defines some properties of binary relations.
Note that antisymmetry is not yet definable, because it requires equality.
---

theory MetaIrreflexive:
	fix (<).
	assume irrefl: ¬ x < x.
end

theory MetaAsymmetric:
	fix (<).
	assume asym: x < y ⟹ ¬ y < x.
end

theory MetaOrder:
	import MetaIrreflexive.
	import MetaTransitive (<).
begin
	interpret MetaAsymmetric;
		for x y if xy: x < y then ¬ y < x;
			apply not_intro;
			if yx: y < x;
				have xx: x < x;
					by trans[OF xy yx].
				by not_imp_false[OF irrefl xx].
			.
		.
end

lemma imp_not: if [P], nQ: ¬Q then ¬(P ⟹ Q);
	apply not_intro;
	if PQ: P ⟹ Q;
		by not_imp_false[OF nQ] PQ.
	.

lemma imp_not_imp: if PQ: P ⟹ Q, nQ: ¬Q then ¬P;
	apply not_intro;
	by not_imp_false[OF nQ] PQ.

lemma imp_not_sym: if PnQ: P ⟹ ¬Q, [Q] then ¬P;
	apply not_intro;
	if !P;
		have nQ: ¬Q;
			by PnQ.
		by not_imp_false[OF nQ].
	.

lemma nnot_intro: if [P] then ¬¬P;
	apply not_intro;
	if nP: ¬P;
		by not_imp_false[OF nP].
	.

lemma not_imp_not_all: if nax: ¬α.[x] then ¬(∀y. α.[y]);
	by not_intro not_imp_false[OF nax].

lemma not_false: ¬false;
	by not_intro[OF imp.refl].

lemma iff_cong_not#cong: if PQ: P ⟺ Q then ¬P ⟺ ¬Q;
	apply iff_intro;
	if nP: ¬P;
		apply not_intro;
		by not_imp_false[OF nP] iff_elim2[OF PQ].
	if nQ: ¬Q;
		apply not_intro;
		by not_imp_false[OF nQ] iff_elim1[OF PQ].
	.

lemma not_iff_imp_false: ¬P ⟺ (P ⟹ false);
	by iff_intro[OF not_imp_false not_intro].

lemma imp_not_commute: (P ⟹ ¬Q) ⟺ (Q ⟹ ¬P);
	by iff_intro[OF imp_not_sym imp_not_sym].

lemma nnnot_iff: ¬¬¬P ⟺ ¬P;
	unfold+ not_iff_imp_false;
	by imp3_iff.

lemma nnot_imp_not_iff: (¬¬P ⟹ ¬Q) ⟺ (P ⟹ ¬Q);
	unfold imp_not_commute;
	unfold nnnot_iff.

lemma nnimp_imp_nnot: if nnPQ: ¬¬(P ⟹ Q), [P] then ¬¬Q;
	apply not_intro;
	if nQ: ¬Q;
		apply+ not_imp_false[OF nnPQ] not_intro;
		if PQ: P ⟹ Q;
			by not_imp_false[OF nQ] PQ.
		.
	.

lemma nnimp_not_iff: ¬¬(P ⟹ ¬Q) ⟺ (P ⟹ ¬Q);
	apply iff_intro;
	if nnimp: ¬¬(P ⟹ ¬Q), P: P then ¬Q;
		by nnimp_imp_nnot[OF nnimp P, unfolded nnnot_iff].
	apply nnot_intro=.

lemma not_true_iff: ¬true ⟺ false;
	apply iff_intro;
	if nt: ¬true;
		by not_imp_false[OF nt].
	by not_intro.

lemma not_false_iff: ¬false ⟺ true;
	by iff_true[OF not_false].

lemma false_imp_false_iff: (false ⟹ false) ⟺ true;
	by iff_true[OF imp.refl].

lemma false_and_false_iff: false ∧ false ⟺ false;
	by iff_intro.

lemma nand_intro1: if nP: ¬P then ¬(P ∧ Q);
	by not_intro not_imp_false[OF nP].

lemma nand_intro2: if nQ: ¬Q then ¬(P ∧ Q);
	by not_intro not_imp_false[OF nQ].

lemma nand_iff_imp_not: ¬(P ∧ Q) ⟺ (P ⟹ ¬Q);
	unfold+ not_iff_imp_false and_imp_iff.

lemma non_contradiction: ¬(P ∧ ¬P);
	unfold nand_iff_imp_not;
	by nnot_intro.

lemma nnot_imp: if imp: ¬¬P ⟹ Q then P ⟹ Q;
	by imp nnot_intro.

lemma nnot_imp_nnot: if nnP: ¬¬P, PQ: P ⟹ Q then ¬¬Q;
	apply not_intro;
	if !¬Q;
		have! ¬P;
			by imp_not_imp[OF PQ].
		by not_imp_false[OF nnP].
	.

lemma nnot_not_imp_nimp: if nnP: ¬¬P, [¬Q] then ¬(P ⟹ Q);
	apply not_intro;
	if PQ: P ⟹ Q;
		have nnQ: ¬¬Q;
			by nnot_imp_nnot[OF nnP PQ].
		by not_imp_false[OF nnQ].
	.

lemma nand_nnot_iff: ¬(P ∧ ¬¬Q) ⟺ ¬(P ∧ Q);
	unfold nand_iff_imp_not nnnot_iff.

lemma nnot_nand_iff: ¬(¬¬P ∧ Q) ⟺ ¬(P ∧ Q);
	unfold iff.and.commute;
	unfold nand_nnot_iff;
	unfold iff.and.commute.

lemma raw_or_imp_iff: ((∀S. (P ⟹ S) ⟹ (Q ⟹ S) ⟹ S) ⟹ R) ⟺ (P ⟹ R) ∧ (Q ⟹ R);
	apply iff_intro;
	if or_imp;
		by or_imp.
	if and: (P ⟹ R) ∧ (Q ⟹ R), or: (∀S. (P ⟹ S) ⟹ (Q ⟹ S) ⟹ S);
		by or[OF and_elim1[OF and] and_elim2[OF and]].
	.

lemma raw_nor_iff_and: ¬(∀R. (P ⟹ R) ⟹ (Q ⟹ R) ⟹ R) ⟺ ¬P ∧ ¬Q;
	unfold+ not_iff_imp_false;
	by raw_or_imp_iff.

lemma nnand_iff: ¬¬(P ∧ Q) ⟺ ¬¬P ∧ ¬¬Q;
	fold nnot_nand_iff;
	fold nand_nnot_iff;
	fold raw_nor_iff_and;
	unfold nnnot_iff;
	unfold raw_nor_iff_and.

---
### Disjunction
---

lemma or_intro: if assm: ∀R. (P ⟹ R) ⟹ (Q ⟹ R) ⟹ R then P ∨ Q;
	by assm[OF or_intro1 or_intro2].

namespace or begin

	interpret MetaSymmetric (∨);
		by or_intro #elim or_elim.

end

lemma or_iff_true1: if ! P then P ∨ Q ⟺ true;
	by iff_intro or_intro1.

lemma or_iff_true2: for P Q if ! Q then P ∨ Q ⟺ true;
	by iff_intro or_intro2.

context iff begin

	namespace or begin

		interpret MetaCompatible (∨);
			for P R Q S if PQ: P ⟺ Q, RS: R ⟺ S then P ∨ R ⟺ Q ∨ S;
				by iff_intro or_intro #elim or_elim #unfold PQ RS.
			.
		note #cong: cong.

		interpret MetaCommAbsorb (∨) true;
			- by iff_intro or_intro.
			- by iff_intro[OF or.sym or.sym].
			.

		interpret MetaAssociative (∨);
			by iff_intro #elim or_elim #unfold or_iff_true1 or_iff_true2.

	end

end

note #cong: iff.or.cong.

lemma imp_or_if: if or: (P ⟹ Q) ∨ (P ⟹ R), [P] then Q ∨ R;
	by or[unfolded imp_imp_iff].

lemma or_imp_iff: (P ∨ Q ⟹ R) ⟺ (P ⟹ R) ∧ (Q ⟹ R);
	apply iff_intro;
	if !;
		by or_intro.
	by #elim or_elim.

lemma nor_iff: ¬(P ∨ Q) ⟺ ¬P ∧ ¬Q;
	unfold+ not_iff_imp_false;
	by or_imp_iff.

lemma nnot_nor_iff: ¬(¬¬P ∨ Q) ⟺ ¬(P ∨ Q);
	unfold+ nor_iff nnnot_iff.

lemma nor_nnot_iff: ¬(P ∨ ¬¬Q) ⟺ ¬(P ∨ Q);
	unfold+ nor_iff nnnot_iff.

lemma nnot_excluded_middle: ¬¬(P ∨ ¬P);
	unfold nor_iff;
	by non_contradiction.

lemma or_imp_nand: if PQ: P ∨ Q then ¬(¬P ∧ ¬Q);
	apply not_intro;
	if and: ¬P ∧ ¬Q;
		have nP: ¬P;
			by and_elim1[OF and].
		have nQ: ¬Q;
			by and_elim2[OF and].
		apply or_elim[OF PQ];
		- by not_imp_false[OF nP].
		- by not_imp_false[OF nQ].
		.
	.

lemma false_or_false_iff: false ∨ false ⟺ false;
	by iff_intro or_intro #elim or_elim.


---
### Existence
---

lemma ex_intro: if assm: ∀P. (∀x. α.[x] ⟹ P) ⟹ P then ∃x. α.[x];
	apply assm;
	for x;
		apply ex_intro1=.
	.

lemma ex_iff: (∃x. α.[x]) ⟺ (∀P. (∀x. α.[x] ⟹ P) ⟹ P);
	apply iff_intro;
	- apply ex_elim=.
	apply ex_intro=.

lemma ex_imp_all_imp: if ex: ∃x. α.[x] ⟹ P, [∀x. α.[x]] then P;
	apply ex_elim[OF ex];
	for x if imp: α.[x] ⟹ P;
		by imp.
	.

lemma all_imp_iff_ex: (∀x. α.[x] ⟹ P) ⟺ (∃x. α.[x]) ⟹ P;
	apply iff_intro;
	if imp: ∀x. α.[x] ⟹ P, ex: ∃x. α.[x];
		obtain x where ax: α.[x];
			for thesis;
				apply ex[unfolded ex_iff, of thesis]=.
			.
		by imp[OF ax].
	if imp: (∃x. α.[x]) ⟹ P;
		for x if ax: α.[x];
			by imp ex_intro1[OF ax].
		.
	.


---
## Double negation and universal quantification.

The following direction is provable in general, but the opposite direction requires something similar to the axiom of choice.
---
lemma nnall_imp: if nnall: ¬¬(∀x. α.[x]) then (∀x. ¬¬α.[x]);
	for x;
		apply not_intro;
		if nax: ¬α.[x];
			by not_imp_false[OF nnall] not_imp_not_all[OF nax].
		.
	.

---
The other direction is provable if inside the quantification has negation.
---

lemma nex_iff_all_not: ¬(∃x. α.[x]) ⟺ (∀x. ¬α.[x]);
	unfold+ not_iff_imp_false;
	fold all_imp_iff_ex.

lemma nnall_not_iff: ¬¬(∀x. ¬α.[x]) ⟺ (∀x. ¬α.[x]);
	fold+ nex_iff_all_not;
	by nnnot_iff.





theory Classes:

	import ..Classes.

	theory Connex:
		fix A (≤).
		assume connex: x ∈ A ⟹ y ∈ A ⟹ x ≤ y ∨ y ≤ x.
	begin

		interpret Reflexive;
			for x if x! x ∈ A then x ≤ x;
				apply or_elim[OF connex[OF x x]].
			.

	end

	theory Irreflexive:
		fix A (<).
		assume irrefl: x ∈ A ⟹ ¬ x < x.
	end

	theory Asymmetric:
		fix A (<).
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

end

