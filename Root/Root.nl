------
# The Root File
------

finalize; -- Root doesn't have any axiom

symbol λ ∧ ∨ ∃ ≠ ! ≤;
symbol solo ¬;

prefix ∀ 0 0;
infix ⟹ 1 0 0;

show mp: if P: P, PQ: P ⟹ Q then Q :=
	by PQ[OF P];

show weaken: if P: P, Q: Q then P :=
	by P;

show ignore: if PQR: (P ⟹ Q) ⟹ R, Q: Q then R :=
	apply PQR;
	show! if P: P then Q :=
		by Q;
	ctxt;
	done;

infix ≤ 51 51 50;

locale MetaReflexive (≤) :=
	assume refl: x ≤ x;
	end;

locale MetaTransitive (≤) :=
	assume trans: x ≤ y ⟹ y ≤ z ⟹ x ≤ z;
	end;

locale MetaPreorder :=
	import MetaReflexive;
	import MetaTransitive;
	end;

infix = 51 51 50;

locale MetaSymmetric (=) :=
	assume sym: x = y ⟹ y = x;
	end;

ctxt MetaPreorder;
locale MetaEquivalence (=) :=
	import MetaSymmetric;
	import MetaPreorder (=);
	end;

infix + 100 101 100;
infix * 110 111 110;

locale MetaCommutative (+) (=) :=
	assume commute: x + y = y + x;
	end;

locale MetaAssociative (+) (=) :=
	assume assoc: x + y + z = x + (y + z);
	end;

locale MetaLeftNeutral (+) (0) (=) :=
	assume left_neutral: 0 + x = x;
	end;

locale MetaRightNeutral (+) (0) (=) :=
	assume right_neutral: x + 0 = x;
	end;

locale MetaLeftAbsorb (*) (0) (=) :=
	assume left_absorb: 0 * x = 0;
	end;

locale MetaRightAbsorb (*) (0) (=) :=
	assume right_absorb: x * 0 = 0;
	end;

---
locale MetaUnitalCommutative (+) (0) (=) :=
	import MetaEquivalence;
	import MetaCommutative;
	import MetaLeftNeutral;
	interpret right: MetaNeutral :=
		discharge x + 0 = x;
			
---
interpret imp: MetaPreorder (⟹) :=
	discharge if P: P then P :=
		by P;
	discharge if PQ: P ⟹ Q, QR: Q ⟹ R, P: P then R :=
		note Q: PQ[OF P];
		by QR[OF Q];
	end;

show imp_commute: if PQR: P ⟹ Q ⟹ R then Q ⟹ P ⟹ R :=
	case Q: Q, P: P :=
		by PQR[OF P Q];
	qed;

show insert: if PQ: P ⟹ Q, RP: R ⟹ P, R: R then Q :=
	by imp_commute[OF imp.trans][OF PQ RP R];

show imp2_imp_imp: if PQQR: ((P ⟹ Q) ⟹ Q) ⟹ R, P: P then R :=
	apply PQQR;
	case PQ: P ⟹ Q :=
		by PQ P;
	qed;

show imp_all: if imp: P ⟹ ∀x. α.[x] then ∀x. P ⟹ α.[x] :=
	case for x, P: P :=
		by imp[OF P];
	qed;

show all_imp: if all: ∀x. P ⟹ α.[x], P: P then ∀x. α.[x] :=
	case for x :=
		by all[OF P];
	qed;

show all_all_imp: if a: ∀x. α.[x], imp: ∀x. α.[x] ⟹ β.[x] then ∀x. β.[x] :=
	case for x :=
		by imp[OF a];
	qed;

-- Obtains true, which is provable.
locale True :=
	obtain true where true_intro: true :=
		case for thesis, assm: ∀true. true ⟹ thesis :=
			by assm(∀x. x ⟹ x)[OF imp.refl];
		qed;
	end;

-- Obtains false, which derives everything, including non-propositions.
locale False :=
	obtain false where false_elim: ∀P. false ⟹ P :=
		case for thesis, assm: ∀false. (∀P. false ⟹ P) ⟹ thesis :=
			show 1: if 2: ∀x. x then P :=
				by 2;
			by assm(∀P. P)[OF 1];
		qed;
	end;

infix ⟺ 1 1 0;
locale Iff (⟺) :=
	assume iff_intro: (P ⟹ Q) ⟹ (Q ⟹ P) ⟹ P ⟺ Q;
	assume iff_elim1: (P ⟺ Q) ⟹ P ⟹ Q;
	assume iff_elim2: (P ⟺ Q) ⟹ Q ⟹ P;
	finalize;
	interpret iff: MetaEquivalence (⟺) :=
		discharge if PQ: P ⟺ Q then Q ⟺ P :=
			by iff_intro[OF iff_elim2[OF PQ] iff_elim1[OF PQ]];
		discharge P ⟺ P :=
			by iff_intro[OF imp.refl imp.refl];
		discharge if PQ: P ⟺ Q, QR: Q ⟺ R then P ⟺ R :=
			note PR: imp.trans[OF iff_elim1[OF PQ] iff_elim1[OF QR]];
			note RP: imp.trans[OF iff_elim2[OF QR] iff_elim2[OF PQ]];
			by iff_intro[OF PR RP];
		end;

	interpret iff_iff: MetaCommutative (⟺) (⟺) :=
		discharge (P ⟺ Q) ⟺ (Q ⟺ P) :=
			by iff_intro[OF iff.sym iff.sym];
		end;

	show imp_imp_iff: if P: P then (P ⟹ Q) ⟺ Q :=
		apply iff_intro;
		case PQ: P ⟹ Q :=
			by PQ[OF P];
		case Q: Q, P2: P :=
			by Q;
		qed;

	show iff_cong_imp: if PQ: P ⟺ Q, RS: R ⟺ S then (P ⟹ R) ⟺ (Q ⟹ S) :=
		apply iff_intro;
		show! if PR: P ⟹ R, Q: Q then S :=
			by iff_elim1[OF RS] PR iff_elim2[OF PQ] Q;
		show! if QS: Q ⟹ S, P: P then R :=
			by iff_elim2[OF RS] QS iff_elim1[OF PQ] P;
		qed;

	show iff_cong_iff: if PQ: P ⟺ Q, RS: R ⟺ S then (P ⟺ R) ⟺ (Q ⟺ S) :=
		apply iff_intro;
		show! if PR: P ⟺ R then Q ⟺ S :=
			show QR: Q ⟺ R :=
				by iff.trans[OF iff.sym[OF PQ] PR];
			by iff.trans[OF QR RS];
		show! if QS: Q ⟺ S then P ⟺ R :=
			show PS: P ⟺ S :=
				by iff.trans[OF PQ QS];
			by iff.trans[OF PS iff.sym[OF RS]];
		qed;

	show iff_cong_all: if ab: ∀x. α.[x] ⟺ β.[x] then (∀x. α.[x]) ⟺ (∀x. β.[x]) :=
		apply iff_intro;
		show! if a: ∀x. α.[x] then ∀x. β.[x] :=
			by iff_elim1[OF ab] a;
		show! if b: ∀x. β.[x] then ∀x. α.[x] :=
			by iff_elim2[OF ab] b;
		qed;

	show imp_iff_iff: if P: P then (P ⟺ Q) ⟺ Q :=
		apply iff_intro;
		case PQ: P ⟺ Q :=
			apply+ iff_elim1[OF PQ] P;
			qed;
		case Q: Q :=
			by iff_intro P Q;
		qed;

	show all_imp2_iff: (∀Q. (P ⟹ Q) ⟹ Q) ⟺ P :=
		apply iff_intro;
		case all: ∀Q. (P ⟹ Q) ⟹ Q :=
			by all[OF imp.refl];
		case P: P :=
			case for Q, PQ: P ⟹ Q :=
				by PQ[OF P];
			qed;
		qed;

	show imp3_iff: (((P ⟹ Q) ⟹ Q) ⟹ Q) ⟺ (P ⟹ Q) :=
		apply iff_intro;
		note! imp2_imp_imp;
		show! if PQ: P ⟹ Q, PQQ: (P ⟹ Q) ⟹ Q then Q :=
			by PQQ[OF PQ];
		qed;

	show imp_all_iff: (P ⟹ ∀x. α.[x]) ⟺ (∀x. P ⟹ α.[x]) :=
		by iff_intro[OF imp_all all_imp];

	show imp_iff_iff1: if P: P then (P ⟺ Q) ⟺ Q :=
		apply iff_intro;
		case PQ: P ⟺ Q :=
			by iff_elim1[OF PQ P];
		case Q: Q :=
			by iff_intro P Q;
		qed;

	end;

infix ∧ 35 36 36;
locale And (∧) :=
	assume and_intro: P ⟹ Q ⟹ P ∧ Q;
	assume and_elim1: P ∧ Q ⟹ P;
	assume and_elim2: P ∧ Q ⟹ Q;
	finalize;
	interpret and: MetaSymmetric (∧) :=
		discharge if PQ: P ∧ Q then Q ∧ P :=
			by and_intro[OF and_elim2[OF PQ] and_elim1[OF PQ]];
		end;
	show and_elim: if PQ: P ∧ Q then ∀R. (P ⟹ Q ⟹ R) ⟹ R :=
		case for R, PQR: P ⟹ Q ⟹ R :=
			by PQR[OF and_elim1[OF PQ] and_elim2[OF PQ]];
		qed;
	end;

prefix ¬ 40 40;
locale MinimalNot false (¬) :=
	assume not_imp_false: ¬ P ⟹ P ⟹ false;
	assume not_intro: (P ⟹ false) ⟹ ¬ P;
	finalize;

	show not_false: ¬false :=
		by not_intro[OF imp.refl];

	show nnot_intro: if P: P then ¬¬P :=
		apply not_intro;
		case nP: ¬P :=
			by not_imp_false[OF nP P];
		qed;

	show nnot_imp: if imp: ¬¬P ⟹ Q, P: P then Q :=
		apply+ imp nnot_intro P;
		qed;

	show imp_not: if P: P, nQ: ¬Q then ¬(P ⟹ Q) :=
		apply not_intro;
		case PQ: P ⟹ Q :=
			note Q: PQ[OF P];
			by not_imp_false[OF nQ Q];
		qed;

	show imp_not_imp: if PQ: P ⟹ Q, nQ: ¬Q then ¬P :=
		apply not_intro;
		show! if P: P then false :=
			by not_imp_false[OF nQ PQ[OF P]];
		qed;

	show imp_not_sym: if PnQ: P ⟹ ¬Q, Q: Q then ¬P :=
		apply not_intro;
		case P: P :=
			show nQ: ¬Q :=
				by PnQ[OF P];
			by not_imp_false[OF nQ Q];
		qed;

	show nnot_imp_nnot: if P: ¬¬P, PQ: P ⟹ Q then ¬¬Q :=
		apply not_intro;
		case nQ: ¬Q :=
			show nP: ¬P :=
				by imp_not_imp[OF PQ nQ];
			by not_imp_false[OF P nP];
		qed;

	show nnimp_imp_nnot: if nnPQ: ¬¬(P ⟹ Q), P: P then ¬¬Q :=
		apply not_intro;
		case nQ: ¬Q :=
			apply+ not_imp_false[OF nnPQ] not_intro;
			case PQ: P ⟹ Q :=
				by not_imp_false[OF nQ] PQ P;
			qed;
		qed;

	show nnot_not_imp_nimp: if P: ¬¬P, nQ: ¬Q then ¬(P ⟹ Q) :=
		apply not_intro;
		case PQ: P ⟹ Q :=
			show Q: ¬¬Q :=
				by nnot_imp_nnot[OF P PQ];
			by not_imp_false[OF Q nQ];
		qed;

	show not_imp_not_all: if nax: ¬α.[x] then ¬(∀y. α.[y]) :=
		apply not_intro;
		case a: ∀y. α.[y] :=
			by not_imp_false[OF nax] a;
		qed;
	end;

locale Not :=
	interpret False;
	import MinimalNot;
	finalize;
	show not_elim: if nP: ¬P, P: P then Q :=
		show f: false :=
			by not_imp_false[OF nP P];
		by false_elim[OF f];
	end;

infix ∨ 30 31 30;
locale Or :=
	fix (∨);
	assume or_intro1: P ⟹ P ∨ Q;
	assume or_intro2: Q ⟹ P ∨ Q;
	assume or_elim: P ∨ Q ⟹ (P ⟹ R) ⟹ (Q ⟹ R) ⟹ R;
	show or_intro: if assm: ∀R. (P ⟹ R) ⟹ (Q ⟹ R) ⟹ R then P ∨ Q :=
		by assm[OF or_intro1 or_intro2];
	interpret or: MetaSymmetric (∨) :=
		discharge if PQ: P ∨ Q then Q ∨ P :=
			by or_elim[OF PQ or_intro2 or_intro1];
		end;
	end;

prefix ∃ 0 0;

locale Ex (∃) :=
	assume ex_intro1: ∀x. ∀α. α.[x] ⟹ ∃x. α.[x];
	assume ex_elim: (∃x. α.[x]) ⟹ (∀x. α.[x] ⟹ P) ⟹ P;

	show ex_intro: if assm: ∀P. (∀x. α.[x] ⟹ P) ⟹ P then ∃x. α.[x] :=
		apply assm;
		note! ex_intro1;
		qed;

	show ex_imp_all_imp: if ex: ∃x. α.[x] ⟹ P, all: ∀x. α.[x] then P :=
		apply ex_elim[OF ex];
		case for x, imp: α.[x] ⟹ P :=
			by imp[OF all];
		qed;
	end;

-----
## For typed logic
-----

locale Reflexive mem (≤) :=
	assume refl: mem x ⟹ x ≤ x;
	end;

locale Symmetric mem (≤) :=
	assume sym: x ≤ y ⟹ mem x ⟹ mem y ⟹ y ≤ x;
	end;

locale Transitive mem (≤) :=
	assume trans: x ≤ y ⟹ y ≤ z ⟹ mem x ⟹ mem y ⟹ mem z ⟹ x ≤ z;
	end;


locale Member mem c :=
	assume type: mem c;
	end;

locale Unary mem f :=
	assume type: mem x ⟹ mem (f x);
	end;

locale Magma mem (+) :=
	assume type: mem x ⟹ mem y ⟹ mem (x + y);
	end;

locale Binder mem ξ :=
	assume type: (∀x. mem α.[x]) ⟹ mem (ξ (x. α.[x]));
	end;


infix ∈ 50 50 50;

locale Collect Collect (∈) :=
	assume in_Collect_iff: x ∈ Collect P ⟺ P x;
	end;
