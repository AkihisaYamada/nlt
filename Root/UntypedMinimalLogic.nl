-----
# Untyped Minimal Logic
-----
base Root;

import TypeFreeMinimal;
import Or;
import Ex;

setup conclude true_intro imp.refl iff.refl;

setup rewrite iff.refl iff.sym iff.trans iff_elim1;

show iff_cong_or: if PQ: P ⟺ Q, RS: R ⟺ S then P ∨ R ⟺ Q ∨ S;
	apply iff_intro;
	show! if PR: P ∨ R then Q ∨ S;
		apply or_elim[OF PR];
		show! if P: P then Q ∨ S;
			show Q: Q; by iff_elim1[OF PQ P];
			by or_intro1[OF Q](S);
		show! if R: R then Q ∨ S;
			show S: S; by iff_elim1[OF RS R];
			by or_intro2[OF S](Q);
		qed;
	show! if QS: Q ∨ S then P ∨ R;
		apply or_elim[OF QS];
		show! if Q: Q then P ∨ R;
			show P: P; by iff_elim2[OF PQ Q];
			by or_intro1[OF P](R);
		show! if S: S then P ∨ R;
			show R: R; by iff_elim2[OF RS S];
			by or_intro2[OF R](P);
		qed;
	qed;

setup cong
	iff_cong_imp: P ⟹ Q,
	iff_cong_iff: P ⟺ Q,
	iff_cong_and: P ∧ Q,
	iff_cong_or: P ∨ Q,
	iff_cong_not: ¬P,
	iff_cong_all! ∀x. α.[x];

show or_commute: P ∨ Q ⟺ Q ∨ P;
	by iff_intro[OF or.sym or.sym];

show or_assoc: P ∨ (Q ∨ R) ⟺ P ∨ Q ∨ R;
	apply iff_intro;
	show! if PQR: P ∨ (Q ∨ R) then P ∨ Q ∨ R;
		apply or_elim[OF PQR];
		show! if P: P then P ∨ Q ∨ R;
			by or_intro1[OF or_intro1[OF P]];
		show! if QR: Q ∨ R then P ∨ Q ∨ R;
			apply or_elim[OF QR];
			show! if Q: Q then P ∨ Q ∨ R;
				by or_intro1[OF or_intro2[OF Q]];
			note! or_intro2;
			qed;
		qed;
	show! if PQR: P ∨ Q ∨ R then P ∨ (Q ∨ R);
		apply or_elim[OF PQR];
		show! if PQ: P ∨ Q then P ∨ (Q ∨ R);
			apply or_elim[OF PQ];
			note! or_intro1;
			show! if Q: Q then P ∨ (Q ∨ R);
				by or_intro2[OF or_intro1[OF Q]];
			qed;
		show! if R: R then P ∨ (Q ∨ R);
			by or_intro2[OF or_intro2[OF R]];
		qed;
	qed;

show or_imp_iff: (P ∨ Q ⟹ R) ⟺ (P ⟹ R) ∧ (Q ⟹ R);
	apply iff_intro;
	case nor: P ∨ Q ⟹ R;
		apply and_intro;
		case P: P;
			by nor[OF or_intro1[OF P]];
		case Q: Q;
			by nor[OF or_intro2[OF Q]];
		qed;
	case and: (P ⟹ R) ∧ (Q ⟹ R), or: P ∨ Q;
		apply or_elim[OF or];
		show! P ⟹ R;
			by and_elim1[OF and];
		show! Q ⟹ R;
			by and_elim2[OF and];
		qed;
	qed;

show nor_iff_and: ¬(P ∨ Q) ⟺ ¬P ∧ ¬Q;
	unfold+ not_iff_imp_false;
	by or_imp_iff;

show nnot_nor_iff: ¬(¬¬P ∨ Q) ⟺ ¬(P ∨ Q);
	unfold+ nor_iff_and nnnot_iff;
	by iff.refl;

show nor_nnot_iff: ¬(P ∨ ¬¬Q) ⟺ ¬(P ∨ Q);
	unfold+ nor_iff_and nnnot_iff;
	by iff.refl;

show nnot_excluded_middle: ¬¬(P ∨ ¬P);
	unfold nor_iff_and;
	by non_contradiction;

show or_imp_nand: if PQ: P ∨ Q then ¬(¬P ∧ ¬Q);
	apply not_intro;
	case and: ¬P ∧ ¬Q;
		apply or_elim[OF PQ];
		show nP: ¬P; by and_elim1[OF and];
		show nQ: ¬Q; by and_elim2[OF and];
		show! if P: P then false;
			by not_imp_false[OF nP P];
		show! if Q: Q then false;
			by not_imp_false[OF nQ Q];
		qed;
	qed;

show false_or_false_iff: false ∨ false ⟺ false;
	apply iff_intro;
	show! if or: false ∨ false then false;
		by or_elim[OF or imp.refl imp.refl];
	show! false ⟹ false ∨ false;
		by or_intro1;
	qed;

show true_or: true ∨ P;
	by or_intro1[OF true_intro];

show or_true: P ∨ true;
	by or.sym[OF true_or];

show iff_cong_ex: if ab: ∀x. α.[x] ⟺ β.[x] then (∃x. α.[x]) ⟺ (∃x. β.[x]);
	apply iff_intro;
	case a: ∃x. α.[x];
		obtain x where ax: α.[x];
			by ex_elim[OF a];
		apply ex_intro1(x);
		by ax[unfolded ab];
	case b: ∃x. β.[x];
		obtain x where bx: β.[x];
			by ex_elim[OF b];
		apply ex_intro1(x);
		by bx[folded ab];
	qed;

setup cong iff_cong_ex! ∃x. α.[x];

show ex_iff_imp2: (∃x. α.[x]) ⟺ (∀P. (∀x. α.[x] ⟹ P) ⟹ P);
	apply iff_intro;
	case ex: ∃x. α.[x];
		by ex_elim[OF ex];
	by ex_intro;

show all_imp_iff_ex_imp: (∀x. α.[x] ⟹ P) ⟺ (∃x. α.[x]) ⟹ P;
	apply iff_intro;
	case imp: ∀x. α.[x] ⟹ P, ex: ∃x. α.[x];
		obtain x where ax: α.[x];
			by ex[unfolded ex_iff_imp2];
		by imp[OF ax];
	case imp: (∃x. α.[x]) ⟹ P;
		case for x, ax: α.[x];
			apply imp;
			by ex_intro1[OF ax];
		qed;
	qed;

show ex_imp_nall: if ex: ∃x. α.[x] then ¬(∀x. ¬α.[x]);
	unfold+ not_iff_imp_false;
	by ex[unfolded ex_iff_imp2];

show ex_not_imp_nall: (∃x. ¬α.[x]) ⟹ ¬(∀x. α.[x]);
	unfold+ not_iff_imp_false;
	by ex_imp_all_imp;

show ex_not_imp_nall_nnot: (∃x. ¬α.[x]) ⟹ ¬(∀x. ¬¬α.[x]);
	by ex_not_imp_nall(x. ¬¬α.[x])[unfolded nnnot_iff];

show nex_iff_all_not: ¬(∃x. α.[x]) ⟺ (∀x. ¬α.[x]);
	unfold+ not_iff_imp_false;
	unfold all_imp_iff_ex_imp;
	by iff.refl;

show nex_nnot_iff: ¬(∃x. ¬¬α.[x]) ⟺ ¬(∃x. α.[x]);
	unfold+ nex_iff_all_not nnnot_iff;
	by iff.refl;

show all_imp_nex: if all: ∀x. α.[x] then ¬(∃x. ¬α.[x]);
	unfold nex_iff_all_not;
	by nnot_intro[OF all];
