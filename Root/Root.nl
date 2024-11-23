------
# The Root File
------

symbol λ ∧ ∨ ∃ ≠ ! ≤;
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

locale MetaReflexive :=
	fix (≤);
	assume refl: x ≤ x;
	end;

locale MetaTransitive :=
	fix (≤);
	assume trans: x ≤ y ⟹ y ≤ z ⟹ x ≤ z;
	end;

locale MetaPreorder :=
	import MetaReflexive;
	import MetaTransitive;
	end;

infix = 51 51 50;

locale MetaSymmetric :=
	fix (=);
	assume sym: x = y ⟹ y = x;
	end;

locale MetaEquivalence :=
	import MetaSymmetric;
	import MetaPreorder (=);
	end;

infix + 100 101 100;

locale MetaCommutative :=
	fix (+) (=);
	assume commute: x + y = y + x;
	end;

locale MetaAssociative :=
	fix (+) (=);
	assume assoc: x + y + z = x + (y + z);
	end;

interpret imp: MetaPreorder (⟹) :=
	discharge if P: P then P;
		by P;
	discharge if PQ: P ⟹ Q, QR: Q ⟹ R, P: P then R;
		note Q: PQ[OF P];
		by QR[OF Q];
	end;

show imp_commute: if PQR: P ⟹ Q ⟹ R then Q ⟹ P ⟹ R;
	case Q: Q, P: P;
		by PQR[OF P Q];
	qed;

show insert: (P ⟹ Q) ⟹ (R ⟹ P) ⟹ R ⟹ Q;
	by imp_commute[OF imp.trans];

show imp2_imp_imp: if PQQR: ((P ⟹ Q) ⟹ Q) ⟹ R, P: P then R;
	apply PQQR;
	by mp[OF P];

show imp_all: if imp: P ⟹ ∀x. α.[x] then ∀x. P ⟹ α.[x];
	show! if P: P then α.[x];
		by imp[OF P];
	qed;

show all_imp: if all: ∀x. P ⟹ α.[x], P: P then ∀x. α.[x];
	by all[OF P];

show all_all_imp: if a: ∀x. α.[x], imp: ∀x. α.[x] ⟹ β.[x] then ∀x. β.[x];
	by imp[OF a];

-- Obtains true, which is provable.
locale True :=
	obtain true where true_intro: true;
		case for thesis, assm: ∀true. true ⟹ thesis;
			by assm(∀x. x ⟹ x)[OF imp.refl];
		qed;
	end;

-- Obtains false, which derives everything, including non-propositions.
locale False :=
	obtain false where false_imp: ∀P. false ⟹ P;
		case for thesis, assm: ∀false. (∀P. false ⟹ P) ⟹ thesis;
			show 1: if 2: ∀x. x then P;
				by 2;
			by assm(∀P. P)[OF 1];
		qed;
	end;

---
The following locale specifies false, which derives any proposition, but not necessarily non-proposition.
This is what usual typed logics assume.
---
locale PropFalse prop false :=
	assume false_imp: prop P ⟹ false ⟹ P;
	end;

infix ⟺ 1 1 0;
locale Iff :=
	fix (⟺);
	assume iff_intro: (P ⟹ Q) ⟹ (Q ⟹ P) ⟹ P ⟺ Q;
	assume iff_elim1: (P ⟺ Q) ⟹ P ⟹ Q;
	assume iff_elim2: (P ⟺ Q) ⟹ Q ⟹ P;
	interpret iff: MetaEquivalence (⟺) :=
		discharge if PQ: P ⟺ Q then Q ⟺ P;
			by iff_intro[OF iff_elim2[OF PQ] iff_elim1[OF PQ]];
		discharge P ⟺ P;
			by iff_intro[OF imp.refl imp.refl];
		discharge if PQ: P ⟺ Q, QR: Q ⟺ R then P ⟺ R;
			note PR: imp.trans[OF iff_elim1[OF PQ] iff_elim1[OF QR]];
			note RP: imp.trans[OF iff_elim2[OF QR] iff_elim2[OF PQ]];
			by iff_intro[OF PR RP];
		end;

	interpret iff_iff: MetaCommutative (⟺) (⟺) :=
		discharge (P ⟺ Q) ⟺ (Q ⟺ P);
			by iff_intro[OF iff.sym iff.sym];
		end;

	show imp_imp_iff: if P: P then (P ⟹ Q) ⟺ Q;
		apply iff_intro;
		case PQ: P ⟹ Q;
			by PQ[OF P];
		case Q: Q, P2: P;
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
			case for x;
				apply iff_elim1[OF ab];
				by a;
			qed;
		show! if b: ∀x. β.[x] then ∀x. α.[x];
			case for x;
				apply iff_elim2[OF ab];
				by b;
			qed;
		qed;

	show imp_iff_iff: if P: P then (P ⟺ Q) ⟺ Q;
		apply iff_intro;
		case PQ: P ⟺ Q;
			apply+ iff_elim1[OF PQ] P;
			qed;
		case Q: Q;
			apply iff_intro;
			case P: P;
				by Q;
			case Q: Q;
				by P;
			qed;
		qed;

	show all_imp2_iff: (∀Q. (P ⟹ Q) ⟹ Q) ⟺ P;
		apply iff_intro;
		case all: ∀Q. (P ⟹ Q) ⟹ Q;
			by all[OF imp.refl];
		case P: P;
			case for Q, PQ: P ⟹ Q;
				by PQ[OF P];
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

	show imp_iff_iff1: if P: P then (P ⟺ Q) ⟺ Q;
		apply iff_intro;
		case PQ: P ⟺ Q;
			by iff_elim1[OF PQ P];
		case Q: Q;
			apply iff_intro;
			case P: P;
				by Q;
			case Q: Q;
				by P;
			qed;
		qed;

	end;

infix ∧ 35 36 36;
locale And :=
	fix (∧);
	assume and_intro: P ⟹ Q ⟹ P ∧ Q;
	assume and_elim1: P ∧ Q ⟹ P;
	assume and_elim2: P ∧ Q ⟹ Q;
	interpret and: MetaSymmetric (∧) :=
		discharge if PQ: P ∧ Q then Q ∧ P;
			by and_intro[OF and_elim2[OF PQ] and_elim1[OF PQ]];
		end;
	show and_elim: if PQ: P ∧ Q then ∀R. (P ⟹ Q ⟹ R) ⟹ R;
		case for R, PQR: P ⟹ Q ⟹ R;
			by PQR[OF and_elim1[OF PQ] and_elim2[OF PQ]];
		qed;
	end;

infix ∨ 30 31 30;
locale Or :=
	fix (∨);
	assume or_intro1: P ⟹ P ∨ Q;
	assume or_intro2: Q ⟹ P ∨ Q;
	assume or_elim: P ∨ Q ⟹ (P ⟹ R) ⟹ (Q ⟹ R) ⟹ R;
	show or_intro: if assm: ∀R. (P ⟹ R) ⟹ (Q ⟹ R) ⟹ R then P ∨ Q;
		by assm[OF or_intro1 or_intro2];
	interpret or: MetaSymmetric (∨) :=
		discharge if PQ: P ∨ Q then Q ∨ P;
			by or_elim[OF PQ or_intro2 or_intro1];
		end;
	end;

prefix ¬ 40 40;
locale Not :=
	fix false (¬);
	assume not_imp_false: ¬ P ⟹ P ⟹ false;
	assume not_intro: (P ⟹ false) ⟹ ¬ P;

	show not_false: ¬false;
		by not_intro[OF imp.refl];

	show nnot_intro: if P: P then ¬¬P;
		apply not_intro;
		case nP: ¬P;
			by not_imp_false[OF nP P];
		qed;

	show nnot_imp: if imp: ¬¬P ⟹ Q, P: P then Q;
		apply imp;
		apply nnot_intro;
		by P;

	show imp_not: if P: P, nQ: ¬Q then ¬(P ⟹ Q);
		apply not_intro;
		case PQ: P ⟹ Q;
			note Q: PQ[OF P];
			by not_imp_false[OF nQ Q];
		qed;

	show imp_not_imp: if PQ: P ⟹ Q, nQ: ¬Q then ¬P;
		apply not_intro;
		show! if P: P then false;
			by not_imp_false[OF nQ PQ[OF P]];
		qed;

	show imp_not_sym: if PnQ: P ⟹ ¬Q, Q: Q then ¬P;
		apply not_intro;
		case P: P;
			show nQ: ¬Q;
				by PnQ[OF P];
			by not_imp_false[OF nQ Q];
		qed;

	show nnot_imp_nnot: if P: ¬¬P, PQ: P ⟹ Q then ¬¬Q;
		apply not_intro;
		case nQ: ¬Q;
			show nP: ¬P;
				by imp_not_imp[OF PQ nQ];
			by not_imp_false[OF P nP];
		qed;

	show nnimp_imp_nnot: if nnPQ: ¬¬(P ⟹ Q), P: P then ¬¬Q;
		apply not_intro;
		case nQ: ¬Q;
			show nPQ: ¬(P ⟹ Q);
				apply not_intro;
				case PQ: P ⟹ Q;
					show Q: Q;
						by PQ[OF P];
					by not_imp_false[OF nQ Q];
				qed;
			by not_imp_false[OF nnPQ nPQ];
		qed;

	show nnot_not_imp_nimp: if P: ¬¬P, nQ: ¬Q then ¬(P ⟹ Q);
		apply not_intro;
		case PQ: P ⟹ Q;
			show Q: ¬¬Q;
				by nnot_imp_nnot[OF P PQ];
			by not_imp_false[OF Q nQ];
		qed;

	show not_imp_not_all: if nax: ¬α.[x] then ¬(∀y. α.[y]);
		apply not_intro;
		case a: ∀y. α.[y];
			show ax: α.[x];
				by a;
			by not_imp_false[OF nax ax];
		qed;
	end;

prefix ∃ 0 0;

locale Ex :=
	fix (∃);
	assume ex_intro1: ∀x. ∀α. α.[x] ⟹ ∃x. α.[x];
	assume ex_elim: (∃x. α.[x]) ⟹ (∀x. α.[x] ⟹ P) ⟹ P;

	show ex_intro: if assm: ∀P. (∀x. α.[x] ⟹ P) ⟹ P then ∃x. α.[x];
		apply assm;
		by ex_intro1;

	show ex_imp_all_imp: if ex: ∃x. α.[x] ⟹ P, all: ∀x. α.[x] then P;
		apply ex_elim[OF ex];
		case for x, imp: α.[x] ⟹ P;
			by imp[OF all];
		qed;

	end;

-----
## Equality
-----

locale Equal :=
	fix (=);
	import eq: MetaReflexive (=);
	assume eq_mono: ∀α. ∀x. ∀y. x = y ⟹ α.[x] ⟹ α.[y];

	interpret eq: MetaEquivalence (=) :=
		discharge if xy: x = y then y = x;
			by eq_mono(z. z = x)[OF xy eq.refl];
		know;
		discharge if xy: x = y, yz: y = z then x = z;
			by eq_mono(w. x = w)[OF yz xy];
		end;

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

	end;

locale Equal_Iff :=
	import Equal;
	import Iff;
	interpret eq_iff: MetaCommutative (=) (⟺) :=
		discharge x = y ⟺ y = x;
			by iff_intro[OF eq.sym eq.sym];
		end;
	setup rewrite eq.refl eq.sym eq.trans eq_prop1;
	setup cong eq_cong: f x;
	show eq_imp_iff: if PQ: P = Q then P ⟺ Q;
		unfold PQ;
		by iff.refl;
	end;

locale Ext :=
	import Equal;
	assume eq_ext: (∀x. α.[x] = β.[x]) ⟹ (x. α.[x]) = (x. β.[x]);
	end;

locale TwoValued :=
	import Equal;
	assume imp_imp_eq: P ⟹ Q ⟹ P = Q;
	assume imp_eq: P ⟹ (P ⟹ Q) = Q;
	end;

-----
## For typed logic
-----

infix ∈ 50 50 50;

locale In :=
	fix (∈);
	end;

locale Collect :=
	fix Collect (∈);
	assume in_Collect_iff: x ∈ Collect P ⟺ P x;
	end;

locale Reflexive :=
	fix mem (≤);
	assume refl: mem x ⟹ x ≤ x;
	end;

locale Symmetric :=
	fix mem (≤);
	assume sym: mem x ⟹ mem y ⟹ x ≤ y ⟹ y ≤ x;
	end;

locale Member :=
	fix mem c;
	assume type: mem c;
	end;

locale Unary :=
	fix mem f;
	assume type: mem x ⟹ mem (f x);
	end;

locale Magma :=
	fix mem (+);
	assume type: mem x ⟹ mem y ⟹ mem (x + y);
	end;

locale Binder :=
	fix mem ξ;
	assume type: (∀x. mem α.[x]) ⟹ mem (ξ (x. α.[x]));
	end;

locale PropOr :=
	fix prop (∨);
	import or: Magma prop (∨);
	assume or_intro1: P ⟹ P ∨ Q;
	assume or_intro2: Q ⟹ P ∨ Q;
	assume or_elim: P ∨ Q ⟹ prop R ⟹ (P ⟹ R) ⟹ (Q ⟹ R) ⟹ R;
	interpret Symmetric prop (∨) :=
		discharge if pP: prop P, pQ: prop Q, or: P ∨ Q then Q ∨ P;
			apply or_elim[OF or];
			apply+ or.type pQ pP;
			by or_intro2 or_intro1;
		end;
	end;

locale PropEx :=
	fix prop (∃);
	import ex: Binder prop (∃);
	assume ex_intro1: ∀x. ∀α. α.[x] ⟹ ∃x. α.[x];
	assume ex_elim: (∃x. α.[x]) ⟹ prop P ⟹ (∀x. α.[x] ⟹ P) ⟹ P;

	show ex_intro:
		if atype: ∀x. prop α.[x],
			assm: ∀P. prop P ⟹ (∀x. α.[x] ⟹ P) ⟹ P
		then ∃x. α.[x];
		apply assm;
		note! ex.type[OF atype];
		by ex_intro1;

	show ex_imp_all_imp: if ex: ∃x. α.[x] ⟹ P, pP: prop P, all: ∀x. α.[x] then P;
		apply ex_elim[OF ex pP];
		case for x, imp: α.[x] ⟹ P;
			by imp[OF all];
		qed;

	end;

locale ExcludedMiddle :=
	fix prop (∨) (¬);
	assume excluded_middle: prop P ⟹ P ∨ ¬P;
	end;