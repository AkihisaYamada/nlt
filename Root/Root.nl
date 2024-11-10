symbol ∀ ⟹ λ ∧ ∨ ∃ = ≠ ! ≤;
symbol solo ¬;

prefix ∀ 0 0;
infix ⟹ 1 0 0;

show mp: if P: P, PQ: P ⟹ Q then Q;
	by PQ[OF P];

show weaken: if P: P, Q: Q then P;
	by P;

infix ≤ 51 51 50;

locale Reflexive {
	fix ≤;
	assume refl: x ≤ x;
}
locale Transitive {
	fix ≤;
	assume trans: x ≤ y ⟹ y ≤ z ⟹ x ≤ z;
}
locale Preorder {
	import Reflexive;
	import Transitive { for _; assume; }
}

infix ~ 51 51 50;

locale Symmetric {
	fix ~;
	assume sym: x ~ y ⟹ y ~ x;
}
locale Equivalence {
	import Symmetric;
	import Preorder { for (~); }
}

import imp: Preorder {
	for (⟹);
	discharge
		fix P;
		assume P: P;
		by P;
	discharge
		fix P Q R;
		assume PQ: P ⟹ Q, QR: Q ⟹ R, P: P;
		note Q: PQ[OF P];
		by QR[OF Q];
}

show imp_commute: if PQR: P ⟹ Q ⟹ R then Q ⟹ P ⟹ R;
	assume Q: Q, P: P;
	by PQR[OF P Q];

show insert: (P ⟹ Q) ⟹ (R ⟹ P) ⟹ R ⟹ Q;
	by imp_commute[OF imp.trans];

show imp_all: if 1: P ⟹ ∀x. α[x] then ∀x. P ⟹ α[x];
	fix x;
	assume P: P;
	by 1[OF P](x);

infix ∧ 35 36 36;
locale And {
	fix ∧;
	assume and_intro: P ⟹ Q ⟹ P ∧ Q;
	assume and_elim1: P ∧ Q ⟹ P;
	assume and_elim2: P ∧ Q ⟹ Q;
	import and: Symmetric {
		for (∧);
		discharge
			fix P Q;
			assume PQ: P ∧ Q;
			by and_intro[OF and_elim2[OF PQ] and_elim1[OF PQ]];
	}
	show and_elim: if PQ: P ∧ Q then ∀R. (P ⟹ Q ⟹ R) ⟹ R;
		fix R;
		assume PQR: P ⟹ Q ⟹ R;
		by PQR[OF and_elim1[OF PQ] and_elim2[OF PQ]];
}

infix ∨ 30 31 30;
locale Or {
	fix ∨;
	assume or_intro1: P ⟹ P ∨ Q;
	assume or_intro2: Q ⟹ P ∨ Q;
	assume or_elim: P ∨ Q ⟹ (P ⟹ R) ⟹ (Q ⟹ R) ⟹ R;
	show or_intro: (∀R. (P ⟹ R) ⟹ (Q ⟹ R) ⟹ R) ⟹ P ∨ Q;
		assume assm: ∀R. (P ⟹ R) ⟹ (Q ⟹ R) ⟹ R;
		by assm[OF or_intro1 or_intro2];
	import or: Symmetric {
		for (∨);
		discharge
			fix P Q;
			assume PQ: P ∨ Q;
			by or_elim[OF PQ or_intro2 or_intro1];
	}
}

prefix ¬ 40 40;
locale Not {
	fix ¬ false;
	assume not_imp_false: ¬ P ⟹ P ⟹ false;
	assume not_intro: (P ⟹ false) ⟹ ¬ P;
	show not_false: ¬false;
		by not_intro[OF imp.refl];

	show imp_not: if P: P, nQ: ¬Q then ¬(P ⟹ Q);
		show 1: if PQ: P ⟹ Q then false;
			show Q: Q; by PQ[OF P];
			by not_imp_false[OF nQ Q];
		by not_intro[OF 1];

	show imp_not_imp: (P ⟹ Q) ⟹ ¬Q ⟹ ¬P;
		assume PQ: P ⟹ Q, nQ: ¬Q;
		show P0: if P: P then false;
			by not_imp_false[OF nQ PQ[OF P]];
		by not_intro[OF P0];

	show not_all: ¬ P x ⟹ ¬(∀y. P y);
		assume nPx: ¬ P x;
		show 1: (∀y. P y) ⟹ false;
			assume 2: ∀y. P y;
			show Px: P x;
				by 2;
			by not_imp_false[OF nPx Px];
		by not_intro[OF 1];

	show NN_imp_NN: ¬¬P ⟹ (P ⟹ Q) ⟹ ¬¬Q;
		assume P: ¬¬P, PQ: P ⟹ Q;
		show nQ0: ¬Q ⟹ false;
			assume nQ: ¬Q;
			show nP: ¬P; by imp_not_imp[OF PQ nQ];
			by not_imp_false[OF P nP];
		by not_intro[OF nQ0];

	show NN_N_nimp: ¬¬P ⟹ ¬Q ⟹ ¬(P ⟹ Q);
		assume P: ¬¬P, nQ: ¬Q;
		show PQ0: (P ⟹ Q) ⟹ false;
			assume PQ: P ⟹ Q;
			show Q: ¬¬Q; by NN_imp_NN[OF P PQ];
			by not_imp_false[OF Q nQ];
		by not_intro[OF PQ0];

	show NN_mp: ¬¬P ⟹ ¬¬(P ⟹ Q) ⟹ ¬¬Q;
		assume P: ¬¬P, PQ: ¬¬(P ⟹ Q);
		show nQ0: ¬Q ⟹ false;
			assume nQ: ¬Q;
			show nPQ: ¬(P ⟹ Q); by NN_N_nimp[OF P nQ];
			by not_imp_false[OF PQ nPQ];
		by not_intro[OF nQ0];

	show not_not: P ⟹ ¬¬P;
		assume P: P;
		show 1: ¬P ⟹ false;
			assume nP: ¬P;
			by not_imp_false[OF nP P];
		by not_intro[OF 1];
}

infix ⟺ 1 1 0;
locale Iff {
	fix ⟺;
	assume iff_intro: (P ⟹ Q) ⟹ (Q ⟹ P) ⟹ P ⟺ Q;
	assume iff_elim1: (P ⟺ Q) ⟹ P ⟹ Q;
	assume iff_elim2: (P ⟺ Q) ⟹ Q ⟹ P;
	import iff: Equivalence {
		for (⟺);
		discharge
			fix P Q;
			assume PQ: P ⟺ Q;
			by iff_intro[OF iff_elim2[OF PQ] iff_elim1[OF PQ]];
		discharge
			by iff_intro[OF imp.refl imp.refl];
		discharge
			fix P Q R;
			assume PQ: P ⟺ Q;
			assume QR: Q ⟺ R;
			note PR: imp.trans[OF iff_elim1[OF PQ] iff_elim1[OF QR]];
			note RP: imp.trans[OF iff_elim2[OF QR] iff_elim2[OF PQ]];
			by iff_intro[OF PR RP];
	}

	show iff_commute: (P ⟺ Q) ⟺ (Q ⟺ P);
		by iff_intro[OF iff.sym iff.sym];

	show imp_imp_iff: if P: P then (P ⟹ Q) ⟺ Q;
		show 1: if PQ: P ⟹ Q then Q;
			by PQ[OF P];
		show 2: if Q: Q, P2: P then Q;
			by Q;
		by iff_intro[OF 1 2];

	show iff_cong_imp: (P ⟺ Q) ⟹ (R ⟺ S) ⟹ (P ⟹ R) ⟺ (Q ⟹ S);
		assume PQ: P ⟺ Q, RS: R ⟺ S;
		show 1: (P ⟹ R) ⟹ (Q ⟹ S);
			assume PR: P ⟹ R;
			show QR: Q ⟹ R; by imp.trans[OF iff_elim2[OF PQ] PR];
			by imp.trans[OF QR iff_elim1[OF RS]];
		show 2: (Q ⟹ S) ⟹ (P ⟹ R);
			assume QS: Q ⟹ S;
			show PS: P ⟹ S; by imp.trans[OF iff_elim1[OF PQ] QS];
			by imp.trans[OF PS iff_elim2[OF RS]];
		by iff_intro[OF 1 2];

	show iff_cong_iff: (P ⟺ Q) ⟹ (R ⟺ S) ⟹ (P ⟺ R) ⟺ (Q ⟺ S);
		assume PQ: P ⟺ Q, RS: R ⟺ S;
		show 1: (P ⟺ R) ⟹ (Q ⟺ S);
			assume PR: P ⟺ R;
			show QR: Q ⟺ R; by iff.trans[OF iff.sym[OF PQ] PR];
			by iff.trans[OF QR RS];
		show 2: (Q ⟺ S) ⟹ (P ⟺ R);
			assume QS: Q ⟺ S;
			show PS: P ⟺ S; by iff.trans[OF PQ QS];
			by iff.trans[OF PS iff.sym[OF RS]];
		by iff_intro[OF 1 2];

}
