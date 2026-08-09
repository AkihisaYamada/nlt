---
# Simple Type of Natural Numbers

## Axiomatization
---
fix ℕ 0 suc rec_nat.

assume nat_type! ℕ : TYPE.
assume 0_nat! 0 : ℕ.
assume suc_type! suc : ℕ → ℕ.

-- Successor is injective in ℕ
assume suc_inj: if suc x = suc y, x : ℕ, y : ℕ then x = y.

---
Induction principle restricted on propositions.
---
assume induction_axiom: ∀x : ℕ, p : ℕ → Prop. p 0 ⟹ (∀x' : ℕ. p x' ⟹ p (suc x')) ⟹ p x.

---
Recursor is parametric to types.
---
assume rec_nat_type! rec_nat A : A → (ℕ → A → A) → ℕ → A.
assume rec_nat_0#simp if z : A, s : ℕ → A → A then rec_nat A z s 0 = z.
assume rec_nat_suc#simp if z : A, s : ℕ → A → A, x : ℕ then rec_nat A z s (suc x) = s x (rec_nat A z s x).

begin

note rec_nat_type1! rec_nat_type[THEN to_elim1].
note rec_nat_type2! rec_nat_type1[THEN to_elim1].
note rec_nat_type3! rec_nat_type2[THEN to_elim1].

lemma induction: for x
	if 0: P.[0], suc: ∀x. P.[x] ⟹ x : ℕ ⟹ P.[suc x], [∀x. x : ℕ ⟹ P.[x] : Prop, x : ℕ]
	then P.[x];
	apply induction_axiom[THEN all_elim1[of x], THEN all_elim1[of (fun x : ℕ. P.[x])], simp];
	by 0 all_intro suc.

instance nat: Equivalence ℕ (=);
	- .
	- by #elim eq.sym.
	- by #intro[after 2] eq.trans.
	.

obtain case_nat where
	case_nat_type! if A : TYPE then case_nat A : A → (ℕ → A) → ℕ → A,
	case_nat_0#simp if A : TYPE, z : A, s : ℕ → A then case_nat A z s 0 = z,
	case_nat_suc#simp  if A : TYPE, z : A, s : ℕ → A, x : ℕ then case_nat A z s (suc x) = s x;
	- for thesis if assm;
		apply assm[of (fun A : TYPE, z : A, s : ℕ → A. rec_nat A z (fun x : ℕ, r : A. s x))].
	.

note case_nat_type1! case_nat_type[THEN to_elim1].
note case_nat_type2! case_nat_type1[THEN to_elim1].
note case_nat_type3! case_nat_type2[THEN to_elim1].

lemma not_0_eq_suc! if [x : ℕ] then ¬ 0 = suc x;
	apply not_intro;
	- if 0: 0 = suc x;
		define is0 = case_nat Prop true (fun x : ℕ. false).
		have eq: false = true;
			.. = is0 (suc x); simp is0_def.
			.. = is0 0; simp 0.
			simp is0_def.
		unfold eq.
	.

obtain funpow where
	funpow_type! if A : TYPE then funpow A : (A → A) → ℕ → A → A,
	funpow_0#simp if A : TYPE, f : A → A, a : A then funpow A f 0 a = a,
	funpow_suc_left: if A : TYPE, f : A → A, n : ℕ, a : A then funpow A f (suc n) a = f (funpow A f n a);
	- for thesis if assm;
		apply assm[of (fun A : TYPE, f : A → A, n : ℕ, a : A. rec_nat A a (fun x : ℕ. f) n)].
	.

note funpow_type1! funpow_type[THEN to_elim1].
note funpow_type2! funpow_type1[THEN to_elim1].
note funpow_type3! funpow_type2[THEN to_elim1].

lemma funpow_suc_right: if [A : TYPE, f : A → A, n : ℕ, a : A] then funpow A f (suc n) a = funpow A f n (f a);
	apply induction[of n];
	- simp funpow_suc_left.
	- for n' if IH, ... then funpow A f (suc (suc n')) a = funpow A f (suc n') (f a);
		.. = f (funpow A f (suc n') a); simp funpow_suc_left.
		.. = f (funpow A f n' (f a)); simp IH.
		simp funpow_suc_left.
	.

definition 1 = suc 0.

lemma 1_nat! 1 : ℕ; by #simp 1_def.

lemma 0_eq_1_elim: ¬ 0 = 1;
	unfold 1_def;
	by not_0_eq_suc.

definition 2 = suc 1.

lemma 2_type! 2 : ℕ; by #simp 2_def.

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
	- .
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

lemma add_2_eq#simp if [x : ℕ] then x + 2 = suc (suc x); simp 2_def.
lemma 2_add_eq#simp if [x : ℕ] then 2 + x = suc (suc x); simp 2_def.

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
---
namespace bits begin

obtain bit0 where
	bit0_nat! if x : ℕ then bit0 x : ℕ,
	bit0_eq: if x : ℕ then bit0 x = 2 * x;
	- for thesis if assm;
		apply assm[of (fun x : ℕ. 2 * x)].
	.
obtain bit1 where
	bit1_nat! if x : ℕ then bit1 x : ℕ,
	bit1_eq: if x : ℕ then bit1 x = 2 * x + 1; 
	- for thesis if assm;
		apply assm[of (fun x : ℕ. 2 * x + 1)].
	.

lemma bit0_add_bit0#simp if [x : ℕ, y : ℕ] then bit0 x + bit0 y = bit0 (x + y);
	simp bit0_eq left_distrib.

lemma bit0_add_bit1#simp if [x : ℕ, y : ℕ] then bit0 x + bit1 y = bit1 (x + y);
	simp bit0_eq bit1_eq left_distrib.

lemma bit1_add_bit0#simp if [x : ℕ, y : ℕ] then bit1 x + bit0 y = bit1 (x + y);
	simp bit0_eq bit1_eq left_distrib.

lemma bit1_add_bit1#simp if [x : ℕ, y : ℕ] then bit1 x + bit1 y = bit0 (suc (x + y));
	simp bit0_eq bit1_eq left_distrib;.

lemma suc_bit0#simp if [x : ℕ] then suc (bit0 x) = bit1 x;
	simp bit0_eq bit1_eq.

lemma suc_bit1#simp if [x : ℕ] then suc (bit1 x) = bit0 (suc x);
	simp bit0_eq bit1_eq.

lemma suc_1_eq_bit0#simp suc 1 = bit0 1;
	simp bit0_eq 2_def.

lemma: bit0 (bit1 (bit0 (bit1 1))) + bit0 (bit1 1) = bit0 (bit0 (bit0 (bit0 (bit0 1)))).

end

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

lemma suc_diff_suc: if x: x : ℕ, [y : ℕ] then suc x ∸ suc y = x ∸ y;
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
