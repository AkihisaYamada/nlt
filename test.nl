base Root;

import And;
import Or;
import Iff;
import MinimalNot;

setup conclude imp.refl iff.refl;

setup rewrite iff.refl iff.sym iff.trans iff_elim1;

show iff_cong_and: (P ⟺ Q) ⟹ (R ⟺ S) ⟹ P ∧ R ⟺ Q ∧ S;
	assume PQ: P ⟺ Q, RS: R ⟺ S;
	show 1: P ∧ R ⟹ Q ∧ S;
		assume PR: P ∧ R;
		show P: P; by and_elim1[OF PR];
		show R: R; by and_elim2[OF PR];
		show Q: Q; by iff_elim1[OF PQ P];
		show S: S; by iff_elim1[OF RS R];
		by and_intro[OF Q S];
	show 2: Q ∧ S ⟹ P ∧ R;
		assume QS: Q ∧ S;
		show Q: Q; by and_elim1[OF QS];
		show S: S; by and_elim2[OF QS];
		show P: P; by iff_elim2[OF PQ Q];
		show R: R; by iff_elim2[OF RS S];
		by and_intro[OF P R];
	by iff_intro[OF 1 2];

show iff_cong_or: (P ⟺ Q) ⟹ (R ⟺ S) ⟹ P ∨ R ⟺ Q ∨ S;
	assume PQ: P ⟺ Q, RS: R ⟺ S;
	show 1: P ∨ R ⟹ Q ∨ S;
		assume PR: P ∨ R;
		show 1.1: P ⟹ Q ∨ S;
			assume P: P;
			show Q: Q; by iff_elim1[OF PQ P];
			by or_intro1[OF Q](S);
		show 1.2: R ⟹ Q ∨ S;
			assume R: R;
			show S: S; by iff_elim1[OF RS R];
			by or_intro2[OF S](Q);
		by or_elim[OF PR 1.1 1.2];
	show 2: Q ∨ S ⟹ P ∨ R;
		assume QS: Q ∨ S;
		show 2.1: Q ⟹ P ∨ R;
			assume Q: Q;
			show P: P; by iff_elim2[OF PQ Q];
			by or_intro1[OF P](R);
		show 2.2: S ⟹ P ∨ R;
			assume S: S;
			show R: R; by iff_elim2[OF RS S];
			by or_intro2[OF R](P);
		by or_elim[OF QS 2.1 2.2];
	by iff_intro[OF 1 2];

show iff_cong_not: (P ⟺ Q) ⟹ ¬P ⟺ ¬Q;
	assume PQ: P ⟺ Q;
	show 1: ¬P ⟹ ¬Q;
		assume nP: ¬P;
		show Q0: Q ⟹ false;
			assume Q: Q;
			show P: P; by iff_elim2[OF PQ Q];
			by not_imp_false[OF nP P];
		by not_intro[OF Q0];
	show 2: ¬Q ⟹ ¬P;
		assume nQ: ¬Q;
		show P0: P ⟹ false;
			assume P: P;
			show Q: Q; by iff_elim1[OF PQ P];
			by not_imp_false[OF nQ Q];
		by not_intro[OF P0];
	by iff_intro[OF 1 2];

setup cong
	P ⟹ Q: iff_cong_imp,
	P ⟺ Q: iff_cong_iff,
	P ∧ Q: iff_cong_and,
	P ∨ Q: iff_cong_or,
	¬P: iff_cong_not;


show and_commute: P ∧ Q ⟺ Q ∧ P;
	by iff_intro[OF and.sym and.sym];

show or_commute: P ∨ Q ⟺ Q ∨ P;
	by iff_intro[OF or.sym or.sym];

show and_assoc: P ∧ (Q ∧ R) ⟺ P ∧ Q ∧ R;
	show 1: P ∧ (Q ∧ R) ⟹ P ∧ Q ∧ R;
		assume PQR: P ∧ (Q ∧ R);
		show P: P; by and_elim1[OF PQR];
		show Q: Q; by and_elim1[OF and_elim2[OF PQR]];
		show R: R; by and_elim2[OF and_elim2[OF PQR]];
		by and_intro[OF and_intro[OF P Q] R];
	show 2: P ∧ Q ∧ R ⟹ P ∧ (Q ∧ R);
		assume PQR: P ∧ Q ∧ R;
		show P: P; by and_elim1[OF and_elim1[OF PQR]];
		show Q: Q; by and_elim2[OF and_elim1[OF PQR]];
		show R: R; by and_elim2[OF PQR];
		by and_intro[OF P and_intro[OF Q R]];
	by iff_intro[OF 1 2];

show or_assoc: P ∨ (Q ∨ R) ⟺ P ∨ Q ∨ R;
	show 1: if PQR: P ∨ (Q ∨ R) then P ∨ Q ∨ R;
		show 1.1: if P: P then P ∨ Q ∨ R;
			by or_intro1[OF or_intro1[OF P]](Q,R);
		show 1.2: if QR: Q ∨ R then P ∨ Q ∨ R;
			show 1.2.1: if Q: Q then P ∨ Q ∨ R;
				by or_intro1[OF or_intro2[OF Q](P)](R);
			show 1.2.2: R ⟹ P ∨ Q ∨ R; by or_intro2;
			by or_elim[OF QR 1.2.1 1.2.2];
		by or_elim[OF PQR 1.1 1.2];
	show 2: if PQR: P ∨ Q ∨ R then P ∨ (Q ∨ R);
		show 1.1: if PQ: P ∨ Q then P ∨ (Q ∨ R);
			show 1.1.1: P ⟹ P ∨ (Q ∨ R); by or_intro1;
			show 1.1.2: if Q: Q then P ∨ (Q ∨ R);
				by or_intro2[OF or_intro1[OF Q](R)](P);
			by or_elim[OF PQ 1.1.1 1.1.2];
		show 1.2: if R: R then P ∨ (Q ∨ R);
			by or_intro2[OF or_intro2[OF R](Q)](P);
		by or_elim[OF PQR 1.1 1.2];
	by iff_intro[OF 1 2];

show or_imp_iff: (P ∨ Q ⟹ R) ⟺ (P ⟹ R) ∧ (Q ⟹ R);
	show 1: if nor: P ∨ Q ⟹ R then (P ⟹ R) ∧ (Q ⟹ R);
		show PR: P ⟹ R;
			assume P: P;
			show or: P ∨ Q; by or_intro1[OF P];
			by nor[OF or];
		show QR: Q ⟹ R;
			assume Q: Q;
			show or: P ∨ Q; by or_intro2[OF Q];
			by nor[OF or];
		by and_intro[OF PR QR];
	show 2: if and: (P ⟹ R) ∧ (Q ⟹ R), or: P ∨ Q then R;
		show PR: P ⟹ R; by and_elim1[OF and];
		show QR: Q ⟹ R; by and_elim2[OF and];
		by or_elim[OF or PR QR];
	by iff_intro[OF 1 2];

show not_iff_imp_false: ¬P ⟺ (P ⟹ false);
	by iff_intro[OF not_imp_false not_intro];

show nor_iff: ¬(P ∨ Q) ⟺ ¬P ∧ ¬Q;
	by or_imp_iff(P)(Q)(false)[folded* not_iff_imp_false];

show not_and1: if nP: ¬P then ¬(P ∧ Q);
	show 1: P ∧ Q ⟹ false;
		assume PQ: P ∧ Q;
		by not_imp_false[OF nP and_elim1[OF PQ]];
	by not_intro[OF 1];

show not_and2: if nQ: ¬Q then ¬(P ∧ Q);
	show 1: P ∧ Q ⟹ false;
		assume PQ: P ∧ Q;
		by not_imp_false[OF nQ and_elim2[OF PQ]];
	by not_intro[OF 1];

show not3: ¬¬¬P ⟺ ¬P;
	show imp: ¬¬¬P ⟹ ¬P;
		assume nnnP: ¬¬¬P;
		show P0: P ⟹ false;
			assume P: P;
			show nnP0: ¬¬P ⟹ false;
				by not_imp_false[OF nnnP];
			by nnP0[OF not_not[OF P]];
		by not_intro[OF P0];
	show if: ¬P ⟹ ¬¬¬P;
		by not_not;
	by iff_intro[OF imp if];

show consistency: ¬(P ∧ ¬P);
	show 1: P ∧ ¬P ⟹ false;
		assume 2: P ∧ ¬P;
		show P: P; by and_elim1[OF 2];
		show nP: ¬P; by and_elim2[OF 2];
		by not_imp_false[OF nP P];
	by not_intro[OF 1];

show nn_excluded_middle: ¬¬(P ∨ ¬P);
	by consistency(¬P)[folded nor_iff];

show or_imp_nand: P ∨ Q ⟹ ¬(¬P ∧ ¬Q);
	assume PQ: P ∨ Q;
	show 2: ¬P ∧ ¬Q ⟹ false;
		assume 3: ¬P ∧ ¬Q;
		show nP: ¬P; by and_elim1[OF 3];
		show nQ: ¬Q; by and_elim2[OF 3];
		show 4: P ⟹ false;
			by not_imp_false[OF nP];
		show 5: Q ⟹ false;
			by not_imp_false[OF nQ];
		by or_elim[OF PQ 4 5];
	by not_intro[OF 2];




show N_nand_N_iff: ¬(¬P ∧ ¬Q) ⟺ ¬¬(P ∨ Q);
	by iff.refl(¬(¬P ∧ ¬Q))[folded(1) nor_iff];

show nnand_imp_NN_and_NN: ¬¬(P ∧ Q) ⟹ ¬¬P ∧ ¬¬Q;
	assume PQ: ¬¬(P ∧ Q);
	show nP0: ¬P ⟹ false;
		assume nP: ¬P;
		show nPQ: ¬(P ∧ Q); by not_and1[OF nP];
		by not_imp_false[OF PQ nPQ];
	show P: ¬¬P; by not_intro[OF nP0];
	show nQ0: ¬Q ⟹ false;
		assume nQ: ¬Q;
		show nPQ: ¬(P ∧ Q); by not_and2[OF nQ];
		by not_imp_false[OF PQ nPQ];
	show Q: ¬¬Q; by not_intro[OF nQ0];
	by and_intro[OF P Q];

show false_and_false_iff: false ∧ false ⟺ false;
	show 1: false ∧ false ⟹ false; by and_elim1;
	show 2: false ⟹ false ∧ false;
		assume 0: false;
		by and_intro[OF 0 0];
	by iff_intro[OF 1 2];

show false_or_false_iff: false ∨ false ⟺ false;
	show 1: false ∨ false ⟹ false;
		assume or: false ∨ false;
		by or_elim[OF or imp.refl imp.refl];
	show 2: false ⟹ false ∨ false;
		by or_intro1;
	by iff_intro[OF 1 2];

obtain true where true_intro: true;
	fix thesis;
	assume assm: ∀true. true ⟹ thesis;
	by assm(∀x. x ⟹ x)[OF imp.refl];

setup conclude true_intro;

show true_imp_iff: (true ⟹ P) ⟺ P;
	by imp_imp_iff[OF true_intro];

show imp_true_iff: (P ⟹ true) ⟺ true;
	show 1: if 1.1: P ⟹ true then true;
		by true_intro;
	show 2: if t: true, P: P then true;
		by true_intro;
	by iff_intro[OF 1 2];

show true_iff_iff: (true ⟺ P) ⟺ P;
	show 1: (true ⟺ P) ⟹ P;
		assume P1: true ⟺ P;
		show P: P; fold P1; done;
		by P;
	show 2: P ⟹ (true ⟺ P);
		assume P: P;
		show 2.1: true ⟹ P;
			by weaken[OF P];
		show 2.2: P ⟹ true;
			by weaken[OF true_intro];
		by iff_intro[OF 2.1 2.2];
	by iff_intro[OF 1 2];

show iff_true_iff: (P ⟺ true) ⟺ P;
	unfold(0) iff_commute;
	by true_iff_iff(P);

note iff_true: iff_elim2[OF iff_true_iff];

show false_imp_false_iff: (false ⟹ false) ⟺ true;
	by iff_true[OF imp.refl];

show not_true_iff: ¬true ⟺ false;
	show 1: if nt: ¬true then false;
		by not_imp_false[OF nt true_intro];
	show 2: if f: false then ¬true;
		show tf: if t: true then false;
			by f;
		by not_intro[OF tf];
	by iff_intro[OF 1 2];

show true_and_iff: true ∧ P ⟺ P;
	show 1: true ∧ P ⟹ P; by and_elim2;
	show 2: if P: P then true ∧ P;
		by and_intro[OF true_intro P];
	by iff_intro[OF 1 2];

show true_and_true: true ∧ true;
	unfold true_and_iff;
	done;

show and_true_iff: P ∧ true ⟺ P;
	unfold and_commute;
	unfold true_and_iff;
	done;

show true_or: true ∨ P;
	by or_intro1[OF true_intro];

show or_true: P ∨ true;
	by or.sym[OF true_or];

