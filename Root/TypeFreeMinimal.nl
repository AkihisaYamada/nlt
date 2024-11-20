-------
# Type-Free Part of Minimal Logic
-------

base Root;

import True;
import And;
import Iff;
import Not;

setup conclude true_intro imp.refl iff.refl;

setup rewrite iff.refl iff.sym iff.trans iff_elim1;

show iff_cong_and: if PQ: P ⟺ Q, RS: R ⟺ S then P ∧ R ⟺ Q ∧ S;
	apply iff_intro;
	show! if PR: P ∧ R then Q ∧ S;
		apply and_intro;
		show P: P; by and_elim1[OF PR];
		show R: R; by and_elim2[OF PR];
		show! Q; by iff_elim1[OF PQ P];
		show! S; by iff_elim1[OF RS R];
		qed;
	show! if QS: Q ∧ S then P ∧ R;
		apply and_intro;
		show Q: Q; by and_elim1[OF QS];
		show S: S; by and_elim2[OF QS];
		show! P; by iff_elim2[OF PQ Q];
		show! R; by iff_elim2[OF RS S];
		qed;
	qed;

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

show iff_true: if P: P then P ⟺ true;
	apply iff_intro;
	case P: P;
		by true_intro;
	case t: true;
		by P;
	qed;

show true_imp_iff: (true ⟹ P) ⟺ P;
	by imp_imp_iff[OF true_intro];

show imp_true_iff: (P ⟹ true) ⟺ true;
	apply iff_intro;
	show! if 1.1: P ⟹ true then true;
		by true_intro;
	show! if t: true, P: P then true;
		by true_intro;
	qed;

show true_iff_iff: (true ⟺ P) ⟺ P;
	apply iff_intro;
	show! if P1: true ⟺ P then P;
		fold P1;
		by true_intro;
	show! if P: P then true ⟺ P;
		unfold iff_true[OF P];
		by iff.refl;
	qed;

show iff_true_iff: (P ⟺ true) ⟺ P;
	unfold(0) iff_commute;
	by true_iff_iff(P);

show and_commute: P ∧ Q ⟺ Q ∧ P;
	by iff_intro[OF and.sym and.sym];

show and_assoc: P ∧ (Q ∧ R) ⟺ P ∧ Q ∧ R;
	apply iff_intro;
	show! if PQR: P ∧ (Q ∧ R) then P ∧ Q ∧ R;
		apply and_intro;
		apply and_intro;
		show! P; by and_elim1[OF PQR];
		show! Q; by and_elim1[OF and_elim2[OF PQR]];
		show! R; by and_elim2[OF and_elim2[OF PQR]];
		qed;
	show! if PQR: P ∧ Q ∧ R then P ∧ (Q ∧ R);
		apply and_intro;
		show! P; by and_elim1[OF and_elim1[OF PQR]];
		show! Q ∧ R;
			apply and_intro;
			show! Q; by and_elim2[OF and_elim1[OF PQR]];
			show! R; by and_elim2[OF PQR];
			qed;
		qed;
	qed;

show and_imp_iff: (P ∧ Q ⟹ R) ⟺ (P ⟹ Q ⟹ R);
	apply iff_intro;
	show! if imp: P ∧ Q ⟹ R, P: P, Q: Q then R;
		apply imp;
		apply and_intro;
		apply P;
		by Q;
	show! if imp: P ⟹ Q ⟹ R, and: P ∧ Q then R;
		apply imp;
		apply and_elim1[OF and];
		by and_elim2[OF and];
	qed;

show and_iff: P ∧ Q ⟺ (∀R. (P ⟹ Q ⟹ R) ⟹ R);
	apply iff_intro;
	case and: P ∧ Q;
		case for R, PQR: P ⟹ Q ⟹ R;
			apply PQR;
			by and_elim1[OF and] and_elim2[OF and];
		qed;
	case all: ∀R. (P ⟹ Q ⟹ R) ⟹ R;
		apply all;
		by and_intro;
	qed;

show true_and_iff: true ∧ P ⟺ P;
	apply iff_intro;
	show! true ∧ P ⟹ P;
		by and_elim2;
	show! if P: P then true ∧ P;
		by and_intro[OF true_intro P];
	qed;

show true_and_true: true ∧ true;
	unfold true_and_iff;
	by true_intro;

show and_true_iff: P ∧ true ⟺ P;
	unfold and_commute;
	unfold true_and_iff;
	by iff.refl;

show iff_iff_and: (P ⟺ Q) ⟺ (P ⟹ Q) ∧ (Q ⟹ P);
	apply iff_intro;
	case PQ: P ⟺ Q;
		apply and_intro;
		by iff_elim1[OF PQ] iff_elim2[OF PQ];
	case and: (P ⟹ Q) ∧ (Q ⟹ P);
		apply and_elim[OF and];
		by iff_intro;
	qed;

show all_and_iff: (∀x. α.[x] ∧ β.[x]) ⟺ (∀x. α.[x]) ∧ (∀x. β.[x]);
	apply iff_intro;
	case ab: ∀x. α.[x] ∧ β.[x];
		apply and_intro;
		case for x;
			by and_elim1[OF ab];
		case for x;
			by and_elim2[OF ab];
		qed;
	unfold and_imp_iff;
	case a: ∀x. α.[x], b: ∀x. β.[x];
		case for x;
			apply and_intro;
			by a b;
		qed;
	qed;

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
	unfold and_commute;
	unfold nand_nnot_iff;
	unfold and_commute;
	by iff.refl;

show raw_or_imp_iff: ((∀S. (P ⟹ S) ⟹ (Q ⟹ S) ⟹ S) ⟹ R) ⟺ (P ⟹ R) ∧ (Q ⟹ R);
	apply iff_intro;
	case or_imp: (∀S. (P ⟹ S) ⟹ (Q ⟹ S) ⟹ S) ⟹ R;
		apply and_intro;
		case P: P;
			apply or_imp;
			show! if PS: P ⟹ S, QS: Q ⟹ S then S;
				by PS[OF P];
			qed;
		case Q: Q;
			apply or_imp;
			show! if PS: P ⟹ S, QS: Q ⟹ S then S;
				by QS[OF Q];
			qed;
		qed;
	case and: (P ⟹ R) ∧ (Q ⟹ R), or: (∀S. (P ⟹ S) ⟹ (Q ⟹ S) ⟹ S);
		apply or;
		show! P ⟹ R;
			by and_elim1[OF and];
		show! Q ⟹ R;
			by and_elim2[OF and];
		qed;
	qed;

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

show all_imp_iff_raw_ex: (∀x. α.[x] ⟹ P) ⟺ (∀Q. (∀x. α.[x] ⟹ Q) ⟹ Q) ⟹ P;
	apply iff_intro;
	case imp: ∀x. α.[x] ⟹ P, ex: ∀Q. (∀x. α.[x] ⟹ Q) ⟹ Q;
		obtain x where ax: α.[x];
			by ex;
		by imp[OF ax];
	case imp: (∀Q. (∀x. α.[x] ⟹ Q) ⟹ Q) ⟹ P;
		case for x, ax: α.[x];
			apply imp;
			case for Q, all: ∀x. α.[x] ⟹ Q;
				by all[OF ax];
			qed;
		qed;
	qed;

show raw_nex_iff_all_not: ¬(∀P. (∀x. α.[x] ⟹ P) ⟹ P) ⟺ (∀x. ¬α.[x]);
	unfold+ not_iff_imp_false;
	fold all_imp_iff_raw_ex;
	by iff.refl;

show nnall_not_iff: ¬¬(∀x. ¬α.[x]) ⟺ (∀x. ¬α.[x]);
	fold+ raw_nex_iff_all_not;
	by nnnot_iff;

ctxt;

