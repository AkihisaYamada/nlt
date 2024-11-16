symbol ∀ ⟹ λ ∧ ∨ ∃ = ≠ ! ≤;
symbol solo ¬;

prefix ∀ 0 0;
infix ⟹ 1 0 0;

show mp: if P: P, PQ: P ⟹ Q then Q;
	by PQ[OF P];

show weaken: if P: P, Q: Q then P;
	by P;

show ignore: if PQR: (P ⟹ Q) ⟹ R, Q: Q then R;
	apply PQR;
	show! if P: P then Q;
		by Q;
	qed;

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

show imp_all: if imp: P ⟹ ∀x. α.[x] then ∀x. P ⟹ α.[x];
	show! if P: P then α.[x];
		by imp[OF P];
	qed;

show all_imp: if all: ∀x. P ⟹ α.[x], P: P then ∀x. α.[x];
	by all[OF P];

locale True {
	obtain true where true_intro: true;
		fix thesis;
		assume assm: ∀true. true ⟹ thesis;
		by assm(∀x. x ⟹ x)[OF imp.refl];
}

locale False {
	obtain false where false_elim: ∀P. false ⟹ P;
		fix thesis;
		assume assm: ∀false. (∀P. false ⟹ P) ⟹ thesis;
		show 1: (∀x. x) ⟹ P;
			assume 2: ∀x. x;
			by 2(P);
		by assm(∀P. P)[OF 1];
}

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
	fix false ¬;
	assume not_imp_false: ¬ P ⟹ P ⟹ false;
	assume not_intro: (P ⟹ false) ⟹ ¬ P;

	show not_false: ¬false;
		by not_intro[OF imp.refl];

	show nnot_intro: if P: P then ¬¬P;
		apply not_intro;
		assume nP: ¬P;
		by not_imp_false[OF nP P];

	show nnot_imp: if imp: ¬¬P ⟹ Q, P: P then Q;
		apply imp;
		apply nnot_intro;
		by P;

	show imp_not: if P: P, nQ: ¬Q then ¬(P ⟹ Q);
		apply not_intro;
		assume PQ: P ⟹ Q;
		note Q: PQ[OF P];
		by not_imp_false[OF nQ Q];

	show imp_not_imp: if PQ: P ⟹ Q, nQ: ¬Q then ¬P;
		apply not_intro;
		show! if P: P then false;
			by not_imp_false[OF nQ PQ[OF P]];
		qed;

	show imp_not_sym: if PnQ: P ⟹ ¬Q, Q: Q then ¬P;
		apply not_intro;
		assume P: P;
		show nQ: ¬Q;
			by PnQ[OF P];
		by not_imp_false[OF nQ Q];

	show not_all: if nPx: ¬ P x then ¬(∀y. P y);
		apply not_intro;
		assume all: ∀y. P y;
		by not_imp_false[OF nPx all];

	show nnot_imp_nnot: if P: ¬¬P, PQ: P ⟹ Q then ¬¬Q;
		apply not_intro;
		assume nQ: ¬Q;
		show nP: ¬P;
			by imp_not_imp[OF PQ nQ];
		by not_imp_false[OF P nP];

	show nnimp_imp_nnot: if nnPQ: ¬¬(P ⟹ Q), P: P then ¬¬Q;
		apply not_intro;
		assume nQ: ¬Q;
		show! false;
			show nPQ: ¬(P ⟹ Q);
				apply not_intro;
				assume PQ: P ⟹ Q;
				show Q: Q;
					by PQ[OF P];
				by not_imp_false[OF nQ Q];
			by not_imp_false[OF nnPQ nPQ];
		qed;

	show nnot_not_imp_nimp: if P: ¬¬P, nQ: ¬Q then ¬(P ⟹ Q);
		apply not_intro;
		assume PQ: P ⟹ Q;
		show Q: ¬¬Q;
			by nnot_imp_nnot[OF P PQ];
		by not_imp_false[OF Q nQ];

}
show imp2_imp_imp: if PQQR: ((P ⟹ Q) ⟹ Q) ⟹ R, P: P then R;
	apply PQQR;
	by mp[OF P];

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
		apply iff_intro;
		show! if PQ: P ⟹ Q then Q;
			by PQ[OF P];
		show! if Q: Q, P2: P then Q;
			by Q;
		qed;

	show iff_cong_imp: if PQ: P ⟺ Q, RS: R ⟺ S then (P ⟹ R) ⟺ (Q ⟹ S);
		apply iff_intro;
		show! if PR: P ⟹ R then Q ⟹ S;
			show QR: Q ⟹ R;
				by imp.trans[OF iff_elim2[OF PQ] PR];
			by imp.trans[OF QR iff_elim1[OF RS]];
		show! if QS: Q ⟹ S then P ⟹ R;
			show PS: P ⟹ S; by imp.trans[OF iff_elim1[OF PQ] QS];
			by imp.trans[OF PS iff_elim2[OF RS]];
		qed;

	show iff_cong_iff: if PQ: P ⟺ Q, RS: R ⟺ S then (P ⟺ R) ⟺ (Q ⟺ S);
		apply iff_intro;
		show! if PR: P ⟺ R then Q ⟺ S;
			show QR: Q ⟺ R; by iff.trans[OF iff.sym[OF PQ] PR];
			by iff.trans[OF QR RS];
		show! if QS: Q ⟺ S then P ⟺ R;
			show PS: P ⟺ S; by iff.trans[OF PQ QS];
			by iff.trans[OF PS iff.sym[OF RS]];
		qed;

	show iff_cong_all: if ab: ∀x. α.[x] ⟺ β.[x] then (∀x. α.[x]) ⟺ (∀x. β.[x]);
		apply iff_intro;
		show! if a: ∀x. α.[x] then ∀x. β.[x];
			fix x;
			show! β.[x];
				apply iff_elim1[OF ab];
				by a;
			qed;
		show! if b: ∀x. β.[x] then ∀x. α.[x];
			fix x;
			show! α.[x];
				apply iff_elim2[OF ab];
				by b;
			qed;
		qed;

	show imp3_iff: (((P ⟹ Q) ⟹ Q) ⟹ Q) ⟺ (P ⟹ Q);
		apply iff_intro;
		note! imp2_imp_imp;
		show! if PQ: P ⟹ Q, PQQ: (P ⟹ Q) ⟹ Q then Q;
			apply PQQ;
			by PQ;
		qed;

	show imp_all_iff: (P ⟹ ∀x. α.[x]) ⟺ (∀x. P ⟹ α.[x]);
		by iff_intro[OF imp_all all_imp];
}

infix = 51 51 50;

locale Equal {
	fix =;
	import eq: Reflexive {
		for (=);
	}
	assume eq_mono: ∀α. ∀x. ∀y. x = y ⟹ α.[x] ⟹ α.[y];

	import eq: Equivalence {
		for (=);
		discharge
			fix x y;
			assume xy: x = y;
			by eq_mono(z. z = x)[OF xy eq.refl];
		discharge
			by eq.refl;
		discharge
			fix x y z;
			assume xy: x = y;
			assume yz: y = z;
thm eq_mono;
thm eq_mono(w. x = w);
thm eq_mono(w. x = w)[OF yz];
			by eq_mono(w. x = w)[OF yz xy];
	}

	show arg_cong: if xy: x = y then f x = f y;
		note 1: eq.refl(f x);
		by eq_mono(z. f x = f z)[OF xy 1];

	show fun_cong: if fg: f = g then f x = g x;
		note 1: eq.refl(f x);
		by eq_mono(h. f x = h x)[OF fg 1];

	show eq_cong: if fg: f = g, xy: x = y then f x = g y;
		show 1: f x = f y;
			by arg_cong[OF xy];
		show 2: f y = g y;
			by fun_cong[OF fg];
		by eq.trans[OF 1 2];

	show eq_prop1: P = Q ⟹ P ⟹ Q;
		by eq_mono(x. x);

	show eq_prop2: if PQ: P = Q then Q ⟹ P;
		by eq_prop1[OF eq.sym[OF PQ]];

}

locale Ext {
	import Equal;
	assume eq_ext: (∀x. α.[x] = β.[x]) ⟹ (x. α.[x]) = (x. β.[x]);
}

prefix λ 0 0;

locale Lambda {
	import Equal;
	fix λ;
	assume beta: (λ) α s = α.[s];
}

prefix ∃ 0 0;

locale Ex {
	fix ∃;
	assume ex_intro1: ∀x. ∀α. α.[x] ⟹ (∃) α;
	assume ex_elim: (∃) α ⟹ (∀x. α.[x] ⟹ P) ⟹ P;

	show ex_intro: if assm: ∀P. (∀x. α.[x] ⟹ P) ⟹ P then (∃) α;
		apply assm;
		by ex_intro1;
}