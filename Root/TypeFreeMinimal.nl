-------
# Type-Free Part of Minimal Logic
-------

base Root;

import PositiveLogic;
import Not;

setup conclude true_intro imp.refl iff.refl;

setup rewrite iff.refl iff.sym iff.trans iff_elim1;

show iff_cong_not: if PQ: P ⟺ Q then ¬P ⟺ ¬Q;
	apply iff_intro;
	show! if nP: ¬P then ¬Q;
		apply not_intro;
		show! if Q: Q then false;
			show P: P; by iff_elim2[OF PQ Q];
			by not_imp_false[OF nP P];
		qed;
	show! if nQ: ¬Q then ¬P;
		apply not_intro;
		show! if P: P then false;
			show Q: Q; by iff_elim1[OF PQ P];
			by not_imp_false[OF nQ Q];
		qed;
	qed;

setup cong
	iff_cong_imp: P ⟹ Q,
	iff_cong_iff: P ⟺ Q,
	iff_cong_and: P ∧ Q,
	iff_cong_not: ¬P,
	iff_cong_all! ∀x. α.[x];

show not_iff_imp_false: ¬P ⟺ (P ⟹ false);
	by iff_intro[OF not_imp_false not_intro];

show nnnot_iff: ¬¬¬P ⟺ ¬P;
	unfold+ not_iff_imp_false;
	by imp3_iff;

show imp_not_commute: (P ⟹ ¬Q) ⟺ (Q ⟹ ¬P);
	apply iff_intro;
	note! imp_not_sym;
	note! imp_not_sym;
	qed;

show not_true_iff: ¬true ⟺ false;
	apply iff_intro;
	show! if nt: ¬true then false;
		by not_imp_false[OF nt true_intro];
	show! if f: false then ¬true;
		apply not_intro;
		case t: true;
			by f;
		qed;
	qed;

show not_false_iff: ¬false ⟺ true;
	by iff_true[OF not_false];

show false_and_false_iff: false ∧ false ⟺ false;
	apply iff_intro;
	show! false ∧ false ⟹ false;
		by and_elim1;
	show! if 0: false then false ∧ false;
		by and_intro[OF 0 0];
	qed;

show false_imp_false_iff: (false ⟹ false) ⟺ true;
	by iff_true[OF imp.refl];

show nand_intro1: if nP: ¬P then ¬(P ∧ Q);
	apply not_intro;
	show! if PQ: P ∧ Q then false;
		by not_imp_false[OF nP and_elim1[OF PQ]];
	qed;

show nand_intro2: if nQ: ¬Q then ¬(P ∧ Q);
	apply not_intro;
	show! if PQ: P ∧ Q then false;
		by not_imp_false[OF nQ and_elim2[OF PQ]];
	qed;

show nand_iff_imp_not: ¬(P ∧ Q) ⟺ (P ⟹ ¬Q);
	unfold+ not_iff_imp_false and_imp_iff;
	by iff.refl;

show non_contradiction: ¬(P ∧ ¬P);
	unfold nand_iff_imp_not;
	by nnot_intro;

---
## Double negation and conjunction.
---

show nnot_imp_not_iff: (¬¬P ⟹ ¬Q) ⟺ (P ⟹ ¬Q);
	unfold imp_not_commute;
	unfold nnnot_iff;
	by imp_not_commute;

show nnimp_not_iff: ¬¬(P ⟹ ¬Q) ⟺ (P ⟹ ¬Q);
	apply iff_intro;
	show! if nnimp: ¬¬(P ⟹ ¬Q), P: P then ¬Q;
		by nnimp_imp_nnot[OF nnimp P][unfolded nnnot_iff];
	by nnot_intro;

show nand_nnot_iff: ¬(P ∧ ¬¬Q) ⟺ ¬(P ∧ Q);
	unfold+ nand_iff_imp_not;
	unfold nnnot_iff;
	by iff.refl;

show nnot_nand_iff: ¬(¬¬P ∧ Q) ⟺ ¬(P ∧ Q);
	unfold and_iff.commute;
	unfold nand_nnot_iff;
	unfold and_iff.commute;
	by iff.refl;

show raw_nor_iff_and: ¬(∀R. (P ⟹ R) ⟹ (Q ⟹ R) ⟹ R) ⟺ ¬P ∧ ¬Q;
	unfold+ not_iff_imp_false;
	by raw_or_imp_iff;

show nnand_iff: ¬¬(P ∧ Q) ⟺ ¬¬P ∧ ¬¬Q;
	fold nnot_nand_iff;
	fold nand_nnot_iff;
	fold raw_nor_iff_and;
	unfold nnnot_iff;
	unfold raw_nor_iff_and;
	by iff.refl;

---
## Double negation and universal quantification.

The following direction is provable in general, but the opposite direction requires something similar to the axiom of choice.
---
show nnall_imp: if nnall: ¬¬(∀x. α.[x]) then (∀x. ¬¬α.[x]);
	case for x;
		apply not_intro;
		case nax: ¬α.[x];
			show nall: ¬(∀x. α.[x]);
				by not_imp_not_all[OF nax];
			by not_imp_false[OF nnall nall];
		qed;
	qed;

---
The other direction is provable if inside the quantification has negation.
---

show raw_nex_iff_all_not: ¬(∀P. (∀x. α.[x] ⟹ P) ⟹ P) ⟺ (∀x. ¬α.[x]);
	unfold+ not_iff_imp_false;
	fold all_imp_iff_raw_ex;
	by iff.refl;

show nnall_not_iff: ¬¬(∀x. ¬α.[x]) ⟺ (∀x. ¬α.[x]);
	fold+ raw_nex_iff_all_not;
	by nnnot_iff;

ctxt;

