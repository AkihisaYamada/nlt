base Root;

import True;
import And;
import Or;
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

show iff_cong_or: if PQ: P ⟺ Q,  RS: R ⟺ S then P ∨ R ⟺ Q ∨ S;
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
	P ⟹ Q: iff_cong_imp,
	P ⟺ Q: iff_cong_iff,
	P ∧ Q: iff_cong_and,
	P ∨ Q: iff_cong_or,
	¬P: iff_cong_not;

show imp_not_commute: (P ⟹ ¬Q) ⟺ (Q ⟹ ¬P);
	apply iff_intro;
	note! imp_not_sym;
	note! imp_not_sym;
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
		apply iff_intro;
		show! true ⟹ P;
			by weaken[OF P];
		show! P ⟹ true;
			by weaken[OF true_intro];
		qed;
	qed;

show iff_true_iff: (P ⟺ true) ⟺ P;
	unfold(0) iff_commute;
	by true_iff_iff(P);

note iff_true: iff_elim2[OF iff_true_iff];

show and_commute: P ∧ Q ⟺ Q ∧ P;
	by iff_intro[OF and.sym and.sym];

show or_commute: P ∨ Q ⟺ Q ∨ P;
	by iff_intro[OF or.sym or.sym];

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

show or_imp_iff: (P ∨ Q ⟹ R) ⟺ (P ⟹ R) ∧ (Q ⟹ R);
	apply iff_intro;
	show! if nor: P ∨ Q ⟹ R then (P ⟹ R) ∧ (Q ⟹ R);
		apply and_intro;
		show! if P: P then R;
			by nor[OF or_intro1[OF P]];
		show! if Q: Q then R;
			by nor[OF or_intro2[OF Q]];
		qed;
	show! if and: (P ⟹ R) ∧ (Q ⟹ R), or: P ∨ Q then R;
		apply or_elim[OF or];
		show! P ⟹ R;
			by and_elim1[OF and];
		show! Q ⟹ R;
			by and_elim2[OF and];
		qed;
	qed;

show not_iff_imp_false: ¬P ⟺ (P ⟹ false);
	by iff_intro[OF not_imp_false not_intro];

show nnnot: ¬¬¬P ⟺ ¬P;
	apply iff_intro;
	show! if nnnP: ¬¬¬P then ¬P;
		apply not_intro;
		show! if P: P then false;
			show nnP0: ¬¬P ⟹ false;
				by not_imp_false[OF nnnP];
			by nnP0[OF nnot_intro[OF P]];
		qed;
	show! ¬P ⟹ ¬¬¬P;
		by nnot_intro;
	qed;

show nnot_imp_not_iff: (¬¬P ⟹ ¬Q) ⟺ (P ⟹ ¬Q);
	apply iff_intro;
	show! if imp: ¬¬P ⟹ ¬Q, P: P then ¬Q;
		apply imp;
		apply nnot_intro;
		by P;
	show! if imp: P ⟹ ¬Q, nnP: ¬¬P then ¬Q;
		by nnot_imp_nnot[OF nnP imp][unfolded nnnot];
	qed;

show nor_iff: ¬(P ∨ Q) ⟺ ¬P ∧ ¬Q;
	unfold+ not_iff_imp_false;
	by or_imp_iff;

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

show nand_iff_imp_false: ¬(P ∧ Q) ⟺ (P ⟹ Q ⟹ false);
	unfold+ not_iff_imp_false and_imp_iff;
	by iff.refl;

show nand_nnot_iff: ¬(P ∧ ¬¬Q) ⟺ ¬(P ∧ Q);
	unfold+ nand_iff_imp_false;
	fold+ not_iff_imp_false;
	unfold nnnot;
	by iff.refl;

show nnot_nand_iff: ¬(¬¬P ∧ Q) ⟺ ¬(P ∧ Q);
	unfold and_commute;
	unfold nand_nnot_iff;
	unfold and_commute;
	by iff.refl;

show non_contradiction: ¬(P ∧ ¬P);
	apply not_intro;
	assume and: P ∧ ¬P;
	show P: P;
		by and_elim1[OF and];
	show nP: ¬P;
		by and_elim2[OF and];
	by not_imp_false[OF nP P];

show nnot_excluded_middle: ¬¬(P ∨ ¬P);
	unfold nor_iff;
	by non_contradiction;

show or_imp_nand: if PQ: P ∨ Q then ¬(¬P ∧ ¬Q);
	apply not_intro;
	assume and: ¬P ∧ ¬Q;
	show! false;
		apply or_elim[OF PQ];
		show nP: ¬P; by and_elim1[OF and];
		show nQ: ¬Q; by and_elim2[OF and];
		show! if P: P then false;
			by not_imp_false[OF nP P];
		show! if Q: Q then false;
			by not_imp_false[OF nQ Q];
		qed;
	qed;

show not_or_imp_imp: if nPQ: ¬P ∨ Q, P: P then Q;
	apply or_elim[OF nPQ];
	show! if nP: ¬P then Q;
		by not_elim[OF nP P];
	show! if Q: Q then Q;
		by Q;
	qed;

show nnand_imp_nnot_and_nnot: if PQ: ¬¬(P ∧ Q) then ¬¬P ∧ ¬¬Q;
	apply and_intro;
	show! ¬¬P;
		apply not_intro;
		assume nP: ¬P;
		show nPQ: ¬(P ∧ Q);
			by nand_intro1[OF nP];
		by not_imp_false[OF PQ nPQ];
	show! ¬¬Q;
		apply not_intro;
		assume nQ: ¬Q;
		show nPQ: ¬(P ∧ Q);
			by nand_intro2[OF nQ];
		by not_imp_false[OF PQ nPQ];
	qed;

show false_and_false_iff: false ∧ false ⟺ false;
	apply iff_intro;
	show! false ∧ false ⟹ false;
		by and_elim1;
	show! if 0: false then false ∧ false;
		by and_intro[OF 0 0];
	qed;

show false_or_false_iff: false ∨ false ⟺ false;
	apply iff_intro;
	show! if or: false ∨ false then false;
		by or_elim[OF or imp.refl imp.refl];
	show! false ⟹ false ∨ false;
		by or_intro1;
	qed;

show false_imp_false_iff: (false ⟹ false) ⟺ true;
	by iff_true[OF imp.refl];

show not_true_iff: ¬true ⟺ false;
	apply iff_intro;
	show! if nt: ¬true then false;
		by not_imp_false[OF nt true_intro];
	show! if f: false then ¬true;
		apply not_intro;
		assume t: true;
		by f;
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

show true_or: true ∨ P;
	by or_intro1[OF true_intro];

show or_true: P ∨ true;
	by or.sym[OF true_or];

