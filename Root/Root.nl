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
	by PQR Q;

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
	- if [P] then P :=
		done;
	- if PQ: P ⟹ Q, QR: Q ⟹ R, [P] then R :=
		by QR PQ;
	end;

show imp_commute: if PQR: P ⟹ Q ⟹ R then Q ⟹ P ⟹ R :=
	by PQR;

show insert: if PQ: P ⟹ Q, RP: R ⟹ P then R ⟹ Q :=
	by PQ RP;

show imp2_imp_imp: if PQQR: ((P ⟹ Q) ⟹ Q) ⟹ R, [P] then R :=
	apply PQQR;
	- if PQ: P ⟹ Q :=
		by PQ;
	qed;

show imp_all: if imp: P ⟹ ∀x. α.[x] then ∀x. P ⟹ α.[x] :=
	- for x, if P: P :=
		by imp[OF P];
	qed;

show all_imp: if all: ∀x. P ⟹ α.[x], [P] then ∀x. α.[x] :=
	by all;

show all_all_imp: if [∀x. α.[x]], imp: ∀x. α.[x] ⟹ β.[x] then ∀x. β.[x] :=
	by imp;

-- Obtains true, which is provable.
locale True :=
	obtain true where true_intro#concl: true :=
		- for thesis, if assm: ∀true. true ⟹ thesis :=
			by assm(∀x. x ⟹ x);
		qed;
	end;

-- Obtains false, which derives everything, including non-propositions.
locale False :=
	obtain false where false_elim: ∀P. false ⟹ P :=
		- for thesis, if assm: ∀false. (∀P. false ⟹ P) ⟹ thesis then thesis :=
			by assm(∀P. P);
		qed;
	end;

infix ⟺ 1 1 0;
locale Iff (⟺) :=
	assume iff_intro: (P ⟹ Q) ⟹ (Q ⟹ P) ⟹ P ⟺ Q;
	assume iff_elim1: (P ⟺ Q) ⟹ P ⟹ Q;
	assume iff_elim2: (P ⟺ Q) ⟹ Q ⟹ P;
	finalize;
	interpret iff: MetaEquivalence (⟺) :=
		- if PQ: P ⟺ Q then Q ⟺ P :=
			by iff_intro[OF iff_elim2[OF PQ] iff_elim1[OF PQ]];
		- P ⟺ P :=
			by iff_intro[OF imp.refl imp.refl];
		- if PQ: P ⟺ Q, QR: Q ⟺ R then P ⟺ R :=
			note PR: imp.trans[OF iff_elim1[OF PQ] iff_elim1[OF QR]];
			note RP: imp.trans[OF iff_elim2[OF QR] iff_elim2[OF PQ]];
			by iff_intro[OF PR RP];
		end;
	note #concl: iff.refl;
	interpret iff_iff: MetaCommutative (⟺) (⟺) :=
		- (P ⟺ Q) ⟺ (Q ⟺ P) :=
			by iff_intro[OF iff.sym iff.sym];
		end;

	show imp_imp_iff: if [P] then (P ⟹ Q) ⟺ Q :=
		apply iff_intro;
		- if PQ: P ⟹ Q :=
			by PQ;
		- := done;
		qed;

	show iff_cong_imp: if PQ: P ⟺ Q, RS: R ⟺ S then (P ⟹ R) ⟺ (Q ⟹ S) :=
		apply iff_intro;
		- if PR: P ⟹ R, [Q] then S :=
			by iff_elim1[OF RS] PR iff_elim2[OF PQ];
		- if QS: Q ⟹ S, [P] then R :=
			by iff_elim2[OF RS] QS iff_elim1[OF PQ];
		qed;

	show iff_cong_iff: if PQ: P ⟺ Q, RS: R ⟺ S then (P ⟺ R) ⟺ (Q ⟺ S) :=
		apply iff_intro;
		- if PR: P ⟺ R then Q ⟺ S :=
			show QR: Q ⟺ R :=
				by iff.trans[OF iff.sym[OF PQ] PR];
			by iff.trans[OF QR RS];
		- if QS: Q ⟺ S then P ⟺ R :=
			show PS: P ⟺ S :=
				by iff.trans[OF PQ QS];
			by iff.trans[OF PS iff.sym[OF RS]];
		qed;

	show iff_cong_all: if ab: ∀x. α.[x] ⟺ β.[x] then (∀x. α.[x]) ⟺ (∀x. β.[x]) :=
		apply iff_intro;
		- if [∀x. α.[x]] then ∀x. β.[x] :=
			by iff_elim1[OF ab];
		- if [∀x. β.[x]] then ∀x. α.[x] :=
			by iff_elim2[OF ab];
		qed;

	show imp_iff_iff: if [P] then (P ⟺ Q) ⟺ Q :=
		apply iff_intro;
		- if PQ: P ⟺ Q :=
			by iff_elim1[OF PQ];
		- := by iff_intro;
		qed;

	show all_imp2_iff: (∀Q. (P ⟹ Q) ⟹ Q) ⟺ P :=
		apply iff_intro;
		- if all: ∀Q. (P ⟹ Q) ⟹ Q :=
			apply all;
			done;
		- if [P] :=
			- for Q, if PQ: P ⟹ Q :=
				by PQ;
			qed;
		qed;

	show imp3_iff: (((P ⟹ Q) ⟹ Q) ⟹ Q) ⟺ (P ⟹ Q) :=
		apply iff_intro;
		- := just imp2_imp_imp;
		- if PQ: P ⟹ Q, PQQ: (P ⟹ Q) ⟹ Q then Q :=
			by PQQ[OF PQ];
		qed;

	show imp_all_iff: (P ⟹ ∀x. α.[x]) ⟺ (∀x. P ⟹ α.[x]) :=
		by iff_intro[OF imp_all all_imp];

	show imp_iff_iff1: if P: P then (P ⟺ Q) ⟺ Q :=
		apply iff_intro;
		- if PQ: P ⟺ Q :=
			by iff_elim1[OF PQ P];
		- if Q: Q :=
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
		- if PQ: P ∧ Q then Q ∧ P :=
			by and_intro and_elim2[OF PQ] and_elim1[OF PQ];
		end;
	show and_elim: if PQ: P ∧ Q then ∀R. (P ⟹ Q ⟹ R) ⟹ R :=
		- for R, if PQR: P ⟹ Q ⟹ R :=
			by PQR and_elim1[OF PQ] and_elim2[OF PQ];
		qed;
	end;

prefix ¬ 40 40;
locale MinimalNot false (¬) :=
	assume not_imp_false: ¬ P ⟹ P ⟹ false;
	assume not_intro: (P ⟹ false) ⟹ ¬ P;
	finalize;

	show not_false: ¬false :=
		by not_intro[OF imp.refl];

	show nnot_intro: if [P] then ¬¬P :=
		apply not_intro;
		- if nP: ¬P :=
			by not_imp_false[OF nP];
		qed;

	show nnot_imp: if imp: ¬¬P ⟹ Q, [P] then Q :=
		by imp nnot_intro;

	show imp_not: if [P], nQ: ¬Q then ¬(P ⟹ Q) :=
		apply not_intro;
		- if PQ: P ⟹ Q :=
			by not_imp_false[OF nQ] PQ;
		qed;

	show imp_not_imp: if PQ: P ⟹ Q, nQ: ¬Q then ¬P :=
		apply not_intro;
		by not_imp_false[OF nQ] PQ;

	show imp_not_sym: if PnQ: P ⟹ ¬Q, [Q] then ¬P :=
		apply not_intro;
		- if P: P :=
			by not_imp_false[OF PnQ[OF P]];
		qed;

	show nnot_imp_nnot: if nnP: ¬¬P, PQ: P ⟹ Q then ¬¬Q :=
		apply not_intro;
		- if [¬Q] :=
			show nP: ¬P :=
				by imp_not_imp[OF PQ];
			by not_imp_false[OF nnP nP];
		qed;

	show nnimp_imp_nnot: if nnPQ: ¬¬(P ⟹ Q), [P] then ¬¬Q :=
		apply not_intro;
		- if nQ: ¬Q :=
			apply+ not_imp_false[OF nnPQ] not_intro;
			- if PQ: P ⟹ Q :=
				by not_imp_false[OF nQ] PQ;
			qed;
		qed;

	show nnot_not_imp_nimp: if nnP: ¬¬P, [¬Q] then ¬(P ⟹ Q) :=
		apply not_intro;
		- if PQ: P ⟹ Q :=
			show nnQ: ¬¬Q :=
				by nnot_imp_nnot[OF nnP PQ];
			by not_imp_false[OF nnQ];
		qed;

	show not_imp_not_all: if nax: ¬α.[x] then ¬(∀y. α.[y]) :=
		by not_intro not_imp_false[OF nax];
	end;

locale Not :=
	interpret False;
	import MinimalNot;
	finalize;
	show not_elim: if nP: ¬P, [P] then Q :=
		show f: false :=
			by not_imp_false[OF nP];
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
		- if PQ: P ∨ Q then Q ∨ P :=
			by or_elim[OF PQ or_intro2 or_intro1];
		end;
	end;

prefix ∃ 0 0;

locale Ex (∃) :=
	assume ex_intro1: ∀x. ∀α. α.[x] ⟹ ∃x. α.[x];
	assume ex_elim: (∃x. α.[x]) ⟹ (∀x. α.[x] ⟹ P) ⟹ P;

	show ex_intro: if assm: ∀P. (∀x. α.[x] ⟹ P) ⟹ P then ∃x. α.[x] :=
		apply assm;
		- for x :=
			just ex_intro1;
		qed;

	show ex_imp_all_imp: if ex: ∃x. α.[x] ⟹ P, [∀x. α.[x]] then P :=
		apply ex_elim[OF ex];
		- for x, if imp: α.[x] ⟹ P :=
			by imp;
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
