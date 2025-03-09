------
# The Root File
------

begin -- Root doesn't have any axiom

symbol λ ∧ ∨ ∃ ≠ ≤;
symbol solo ¬;

infix ⟹ 1 0 0;
binder ∀ 0 0;

prefix ¬ 40 40;
infix ∧ 35 36 36;
infix ∨ 30 31 30;
infix ⟺ 1 1 0;
binder ∃ 0 0;

infix = 51 51 50;
infix ≠ 51 51 50;
infix < 51 51 50;
infix > 51 51 50;
infix ≤ 51 51 50;
infix ≥ 51 51 50;

infix + 100 101 100;
infix * 110 111 110;


lemma mp: if P: P, PQ: P ⟹ Q then Q :=
	by PQ[OF P];

lemma weaken: if P: P, Q: Q then P :=
	by P;

lemma ignore: if PQR: (P ⟹ Q) ⟹ R, Q: Q then R :=
	by PQR Q;


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

locale MetaSymmetric (=) :=
	assume sym: x = y ⟹ y = x;
	end;

locale MetaEquivalence (=) :=
	import MetaSymmetric;
	import MetaPreorder (=);
	end;

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
	- done;
	- for P Q R, if PQ: P ⟹ Q, QR: Q ⟹ R, [P] then R :=
		by QR PQ;
	done;

lemma imp_commute: if PQR: P ⟹ Q ⟹ R then Q ⟹ P ⟹ R :=
	by PQR;

lemma insert: if PQ: P ⟹ Q, RP: R ⟹ P then R ⟹ Q :=
	by PQ RP;

lemma imp2_imp_imp: if PQQR: ((P ⟹ Q) ⟹ Q) ⟹ R, [P] then R :=
	apply PQQR;
	- if PQ: P ⟹ Q :=
		by PQ;
	done;

lemma imp_all: if imp: P ⟹ ∀x. α.[x] then ∀x. P ⟹ α.[x] :=
	- for x, if P: P :=
		by imp[OF P];
	done;

lemma all_imp: if all: ∀x. P ⟹ α.[x], [P] then ∀x. α.[x] :=
	by all;

lemma all_all_imp: if [∀x. α.[x]], imp: ∀x. α.[x] ⟹ β.[x] then ∀x. β.[x] :=
	by imp;

-- Obtains true, which is provable.
locale True :=
	obtain true where true_intro! true :=
		- for thesis, if assm: ∀true. true ⟹ thesis :=
			by assm(∀x. x ⟹ x);
		done;
	end;

-- Obtains false, which derives everything, including non-propositions.
locale False :=
	obtain false where false_elim: false ⟹ ∀P. P :=
		- for thesis, if assm: ∀false. (false ⟹ ∀P. P) ⟹ thesis then thesis :=
			by assm(∀P. P);
		done;
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

locale TypedBinder mem ξ :=
	assume type: (∀x. ι x ⟹ mem α.[x]) ⟹ mem (ξ ι (x. α.[x]));
	end;

locale Commutative mem (+) (=) :=
	assume commute: mem x ⟹ mem y ⟹ x + y = y + x;
	end;

locale Associative mem (+) (=) :=
	assume assoc: mem x ⟹ mem y ⟹ mem z ⟹ x + y + z = x + (y + z);
	end;

locale LeftNeutral mem (+) (0) (=) :=
	assume left_neutral: mem x ⟹ 0 + x = x;
	end;

locale RightNeutral mem (+) (0) (=) :=
	assume right_neutral: mem x ⟹ x + 0 = x;
	end;

locale LeftAbsorb mem (*) (0) (=) :=
	assume left_absorb: mem x ⟹ 0 * x = 0;
	end;

locale RightAbsorb mem (*) (0) (=) :=
	assume right_absorb: mem x ⟹ x * 0 = 0;
	end;

infix ∈ 50 50 50;

locale Collect Collect (∈) :=
	assume in_Collect_iff: x ∈ Collect P ⟺ P x;
	end;

