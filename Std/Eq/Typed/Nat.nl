---
# First-Order Intuitionistic Natural Numbers

Natural number theory requires at least first-order intuitionistic logic.
Moreover, function abstraction is almost necessary, since otherwise recursive definitions must be always axiomatized.
---
import FirstOrder, Intuitionistic, FunTo (fun_:).
---
## Axiomatization
---
fix ℕ 0 suc rec_nat.

assume nat_ind! ℕ : IND.-- Quantification over ℕ is allowed.
assume nat_eqtype! ℕ : EQTYPE.-- Equality over naturals is a proposition.

assume 0_nat! 0 : ℕ.
assume suc_to! suc : ℕ → ℕ.

-- Successor is injective in ℕ
assume suc_inj: if suc x = suc y, x : ℕ, y : ℕ then x = y.

---
Induction principle restricted on propositions.
Since we are not in a higher-order logic, this principle is an axiom schema parametric to `P`. 
---
assume induction_axioms:
	if ∀x. x : ℕ ⟹ P.[x] : Prop
	then P.[0] ⟹ (∀x : ℕ. P.[x] ⟹ P.[suc x]) ⟹ ∀x : ℕ. P.[x].

---
Recursor is parametric to types. Since the specification is equality, the type is restricted to `EQTYPE`.
---
assume rec_nat_type!
	if A : EQTYPE
	then rec_nat A : A → (ℕ → A → A) → ℕ → A.

assume rec_nat_0#simp
	if A : EQTYPE, z : A, s : ℕ → A → A
	then rec_nat A z s 0 = z.

assume rec_nat_suc#simp
	if A : EQTYPE, z : A, s : ℕ → A → A, x : ℕ
	then rec_nat A z s (suc x) = s x (rec_nat A z s x).

begin

note nat_eq_prop! eq_prop[OF nat_eqtype].-- TODO don't export

instance nat: Equivalence ℕ (=);
	- .
	- by #elim eq.sym.
	- by #intro[after 2] eq.trans.
	.

note rec_nat_type1! rec_nat_type[THEN to_elim1].
note rec_nat_type2! rec_nat_type1[THEN to_elim1].
note rec_nat_type3! rec_nat_type2[THEN to_elim1].

lemma induction: for x
	if 0: P.[0], suc: ∀x. P.[x] ⟹ x : ℕ ⟹ P.[suc x], [∀x. x : ℕ ⟹ P.[x] : Prop, x : ℕ]
	then P.[x];
	apply induction_axioms[of P, THEN all_elim1[of x]];
	by 0 all_intro suc.

obtain case_nat where
	case_nat_type! if A : EQTYPE then case_nat A : A → (ℕ → A) → ℕ → A,
	case_nat_0#simp if A : EQTYPE, z : A, s : ℕ → A then case_nat A z s 0 = z,
	case_nat_suc#simp  if A : EQTYPE, z : A, s : ℕ → A, x : ℕ then case_nat A z s (suc x) = s x;
	- for thesis if assm;
		apply assm[of (fun A : EQTYPE, z : A, s : ℕ → A. rec_nat A z (fun x : ℕ, r : A. s x))].
	.

note case_nat_type1! case_nat_type[THEN to_elim1].
note case_nat_type2! case_nat_type1[THEN to_elim1].
note case_nat_type3! case_nat_type2[THEN to_elim1].

lemma not_0_eq_suc: if [x : ℕ] then ¬ 0 = suc x;
	apply not_intro;
	- if 0: 0 = suc x;
		define is0 = case_nat Prop true (fun x : ℕ. false).
		have eq: false = true;
			.. = is0 (suc x); simp is0_def.
			.. = is0 0; simp 0.
			simp is0_def.
		unfold eq.
	by nat_eq_prop.

lemma 

obtain funpow where
	funpow_type! if A : EQTYPE then funpow A : (A → A) → ℕ → A → A,
	funpow_0#simp if A : EQTYPE, f : A → A, a : A then funpow A f 0 a = a,
	funpow_suc_left: if A : EQTYPE, f : A → A, n : ℕ, a : A then funpow A f (suc n) a = f (funpow A f n a);
	- for thesis if assm;
		apply assm[of (fun A : EQTYPE, f : A → A, n : ℕ, a : A. rec_nat A a (fun x : ℕ. f) n)].
	.

note funpow_type1! funpow_type[THEN to_elim1].
note funpow_type2! funpow_type1[THEN to_elim1].
note funpow_type3! funpow_type2[THEN to_elim1].

lemma funpow_suc_right: if [A : EQTYPE, f : A → A, n : ℕ, a : A] then funpow A f (suc n) a = funpow A f n (f a);
	apply induction[of n];
	- simp funpow_suc_left.
	- for n' if IH, ... then funpow A f (suc (suc n')) a = funpow A f (suc n') (f a);
		.. = f (funpow A f (suc n') a); simp funpow_suc_left.
		.. = f (funpow A f n' (f a)); simp IH.
		simp funpow_suc_left.
	by eq_prop[of A].

definition 1 = suc 0.

lemma 1_nat! 1 : ℕ; by #simp 1_def.

lemma 0_eq_1_elim: ¬ 0 = 1;
	unfold 1_def;
	by not_0_eq_suc.

obtain (+) where
	add_nat! if x : ℕ, y : ℕ then x + y : ℕ,
	add_0#simp if x : ℕ then x + 0 = x,
	add_suc#simp if x : ℕ, y : ℕ then x + suc y = suc (x + y);
	- for thesis if assm;
		apply assm[of (fun x : ℕ. rec_nat ℕ x (fun z : ℕ. suc))].
	.

lemma 0_add#simp if [x : ℕ] then 0 + x = x;
	apply induction[of x];
	- if #simp 0 + x' = x', ... then 0 + suc x' = suc x'.
	.

lemma suc_add#simp if x: x : ℕ, [y : ℕ] then suc x + y = suc (x + y);
	apply arbitrary[OF x];
	apply induction[of y];
	-.
	- for y' if IH, ...;
		by #simp IH[THEN all_elim1].
	.

lemma add_1_eq#simp if [x : ℕ] then x + 1 = suc x; simp 1_def.
lemma 1_add_eq#simp if [x : ℕ] then 1 + x = suc x; simp 1_def.

lemma suc_eq_add_1: if [x : ℕ] then suc x = x + 1.

instance add: nat.CommMonoid (+) 0;
	- if [x : ℕ, y : ℕ] then x + y = y + x;
		apply induction[of x];
		- if IH: x' + y = y + x', ...; simp IH.
		.
	- if [x : ℕ, y : ℕ, z : ℕ] then x + y + z = x + (y + z);
		apply induction[of x];
		- if IH: x' + y + z = x' + (y + z), ...; simp IH.
		.
	.

obtain (*) where
	mul_nat! if x : ℕ, y : ℕ then x * y : ℕ,
	mul_0#simp if x : ℕ then x * 0 = 0,
	mul_suc#simp if x : ℕ, y : ℕ then x * suc y = x + (x * y);
	- for thesis if assm;
		apply assm[of (fun x : ℕ. rec_nat ℕ 0 (fun z y : ℕ. x + y))].
	.

lemma 0_mul#simp if [x : ℕ] then 0 * x = 0;
	apply induction[of x];
	- if #simp 0 * x' = 0, ...; .
	.

lemma suc_mul#simp if x: x : ℕ, [y : ℕ] then suc x * y = x * y + y;
	apply arbitrary[OF x];
	apply induction[of y];
	- for y' if IH, ...;
		by #simp IH[THEN all_elim1] add.left_assoc.
	.

instance nat.CommSemiringNeutral (*) (+) 0 1;
	show distrib: if [x : ℕ, y : ℕ, z : ℕ] then x * (y + z) = x * y + x * z;
		apply induction[of x];
		- if #simp x' * (y + z) = x' * y + x' * z, ...
		  then suc x' * (y + z) = suc x' * y + suc x' * z;
			.. = x' * y + (x' * z + y) + z; simp add.left_assoc.
			have 1: x' * z + y = y + x' * z; by add.commute.
			unfold 1;
			simp add.left_assoc.
		.
	show commute: if [x : ℕ, y : ℕ] then x * y = y * x;
		apply induction[of x];
		- if IH: x' * y = y * x', ...; simp IH; unfold[at 0] add.commute.
		.

	- if [x : ℕ, y : ℕ, z : ℕ] then x * y * z = x * (y * z);
		apply induction[of z];
		- if IH: x * y * z' = x * (y * z'), ...;
			simp IH distrib.
		.
	- if #simp y = y', [x : ℕ, y : ℕ, y' : ℕ] then x + y = x + y'.
	- if [x : ℕ] then 1 * x = x;
		simp 1_def.
	.

note#simp mul.left_neutral mul.right_neutral.

---
## Binary Representation

Numeric literals are internally expressed via `_bit0` and `_bit1`.
---

obtain _bit0 where
	_bit0_nat! if x : ℕ then _bit0 x : ℕ,
	_bit0_eq: if x : ℕ then _bit0 x = suc 1 * x;
	- for thesis if assm;
		apply assm[of (fun x : ℕ. suc 1 * x)].
	.
obtain _bit1 where
	_bit1_nat! if x : ℕ then _bit1 x : ℕ,
	_bit1_eq: if x : ℕ then _bit1 x = suc 1 * x + 1; 
	- for thesis if assm;
		apply assm[of (fun x : ℕ. suc 1 * x + 1)].
	.

lemma _bit0_add_bit0#simp if [x : ℕ, y : ℕ] then _bit0 x + _bit0 y = _bit0 (x + y);
	simp _bit0_eq left_distrib.

lemma _bit0_add_bit1#simp if [x : ℕ, y : ℕ] then _bit0 x + _bit1 y = _bit1 (x + y);
	simp _bit0_eq _bit1_eq left_distrib.

lemma _bit1_add_bit0#simp if [x : ℕ, y : ℕ] then _bit1 x + _bit0 y = _bit1 (x + y);
	simp _bit0_eq _bit1_eq left_distrib.

lemma _bit1_add_bit1#simp if [x : ℕ, y : ℕ] then _bit1 x + _bit1 y = _bit0 (suc (x + y));
	.. = suc (suc (x + x + (y + y))); simp _bit1_eq.
	.. = suc (suc (x + (x + y) + y)); simp add.left_assoc.
	.. = suc (suc (x + (y + x) + y));
		have 1: x + y = y + x; by add.commute.
		unfold 1.
	simp _bit0_eq add.left_assoc.

lemma suc_bit0#simp if [x : ℕ] then suc (_bit0 x) = _bit1 x;
	simp _bit0_eq _bit1_eq.

lemma suc_bit1#simp if [x : ℕ] then suc (_bit1 x) = _bit0 (suc x);
	simp _bit0_eq _bit1_eq.

lemma suc_1_eq_bit0#simp suc 1 = _bit0 1;
	simp _bit0_eq.

lemma _bit0_mul: if [x : ℕ, y: ℕ] then _bit0 x * y = _bit0 (x * y);
	simp _bit0_eq right_distrib.

lemma mul_bit0: if [x : ℕ, y: ℕ] then x * _bit0 y = _bit0 (x * y);
	simp _bit0_eq left_distrib.

lemma _bit1_mul: if [x : ℕ, y: ℕ] then _bit1 x * y = _bit0 (x * y) + y;
	simp _bit1_eq _bit0_eq right_distrib.

lemma mul_bit1: if [x : ℕ, y: ℕ] then x * _bit1 y = _bit0 (x * y) + x;
	simp _bit1_eq _bit0_eq left_distrib.

lemma _bit0_mul_bit0: if [x : ℕ, y: ℕ] then _bit0 x * _bit0 y = _bit0 (_bit0 (x * y));
	simp _bit0_mul mul_bit0.

lemma _bit0_mul_bit1: if [x : ℕ, y: ℕ] then _bit0 x * _bit1 y = _bit0 (_bit0 (x * y) + x);
	simp _bit0_mul mul_bit1.

lemma _bit1_mul_bit0: if [x : ℕ, y: ℕ] then _bit1 x * _bit0 y = _bit0 (_bit0 (x * y) + y);
	simp _bit1_mul mul_bit0.

lemma _bit1_mul_bit1: if [x : ℕ, y: ℕ] then _bit1 x * _bit1 y = _bit1 (_bit0 (x * y) + x + y);
	simp _bit1_mul mul_bit1.

---
### Subtraction
---

definition pred = case_nat ℕ 0 (fun p : ℕ. p).

lemma pred_type! pred : ℕ → ℕ;
	have! (fun p : ℕ. p) : ℕ → ℕ.
	unfold pred_def.

lemma pred_0#simp pred 0 = 0;
	simp pred_def.

lemma pred_suc#simp if [x : ℕ] then pred (suc x) = x;
	simp pred_def.

infix ∸ 100 101 100.

obtain (∸) where
	diff_nat! if x : ℕ, y : ℕ then x ∸ y : ℕ,
	diff_0#simp if x : ℕ then x ∸ 0 = x,
	diff_suc: if x : ℕ, y : ℕ then x ∸ suc y = pred (x ∸ y);
	- for thesis if assm;
		apply assm[of (fun x : ℕ. rec_nat ℕ x (fun _ r : ℕ. pred r))];
		have! (fun _ r : ℕ. pred r) : ℕ → ℕ → ℕ.
		.
	.

lemma 0_diff#simp if [x : ℕ] then 0 ∸ x = 0;
	apply induction[of x];
	- .
	- for x' if IH, ...;
		by #simp IH diff_suc.
	.

lemma suc_diff_suc#simp if x: x : ℕ, [y : ℕ] then suc x ∸ suc y = x ∸ y;
	apply arbitrary[OF x];
	apply induction[of y];
	- apply all_intro;
		- if [x' : ℕ];
			apply induction[of x'];
			- simp diff_suc.
			- for z if IH, ...; simp IH diff_suc.
			.
		.
	- for y' if IH, ...;
		apply all_intro;
		- for x' if ...;
			unfold diff_suc;
			unfold IH[THEN all_elim1, OF ! !].
		.
	.

instance add: nat.MagmaRightCancel (+) (∸);
	- if eq: x = x'; by #simp eq.
	- if x: x : ℕ, [y : ℕ] then x + y ∸ y = x;
		apply arbitrary[OF x];
		apply induction[of y];
		-.
		- for y' if IH, ...;
			apply all_intro;
			- if [x' : ℕ] then x' + suc y' ∸ suc y' = x';
				.. = pred (suc x' + y' ∸ y'); simp diff_suc.
				simp IH[THEN all_elim1].
			.
		.
	.

---
### Ordering
---
obtain (≤) where
	le_nat: if x : ℕ, y : ℕ then (x ≤ y) : Prop,
	le_0: if x : ℕ then x ≤ 0 ⟺ x = 0, 
	suc_le: if x : ℕ, y : ℕ then suc x ≤ suc y ⟺ x ≤ y;
- for thesis if assm;
	apply assm[of (fun x y : ℕ. x ∸ y = 0)].
.

obtain (<) where
	lt_nat: if x : ℕ, y : ℕ then (x < y) : Prop,
	not_lt_0: if x : ℕ then ¬ x < 0, 
	suc_lt: if x : ℕ, y : ℕ then suc x < suc y ⟺ x < y;
- for thesis if assm;
	note! le_nat.
	apply assm[of (fun x y : ℕ. suc x ≤ y)];
	-.
	- if [x : ℕ];
		simp;
		unfold[on (⟺)] le_0;
	- if [x : ℕ, y : ℕ];
		by  #simp le_0 suc_le.
.
