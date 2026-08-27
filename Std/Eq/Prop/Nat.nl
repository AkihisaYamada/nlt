---
# First-Order Intuitionistic Natural Numbers

Natural number theory requires at least first-order intuitionistic logic.
Moreover, function abstraction is almost necessary, since otherwise recursive definitions must be always axiomatized.
---
import Intuitionistic, FirstOrder, FunTo (fun_:).
---
## Axiomatization
---
fix ℕ 0 suc nat_rec.

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
assume nat_induction_axioms:
	if ∀x. x : ℕ ⟹ P.[x] : Prop
	then P.[0] ⟶ (∀x : ℕ. P.[x] ⟶ P.[suc x]) ⟶ ∀x : ℕ. P.[x].

---
Recursor is parametric to types. Since the specification is equality, the type is restricted to `EQTYPE`.
---
assume nat_rec_type!
	if A : EQTYPE
	then nat_rec A : A → (ℕ → A → A) → ℕ → A.

assume nat_rec_0#simp
	if A : EQTYPE, z : A, s : ℕ → A → A
	then nat_rec A z s 0 = z.

assume nat_rec_suc#simp
	if A : EQTYPE, z : A, s : ℕ → A → A, x : ℕ
	then nat_rec A z s (suc x) = s x (nat_rec A z s x).

begin

note nat_eq_prop: eq_prop[OF nat_eqtype].

instance nat: Equivalence ℕ (=);
	- .
	- by #elim eq.sym.
	- by #intro[after 2] eq.trans.
	.

lemma suc_eq_suc#simp if [x : ℕ, y : ℕ] then suc x = suc y ⟷ x = y;
	apply iff_intro;
	- by #elim suc_inj.
	- if #simp.
	by nat_eq_prop.

note nat_rec_type1! nat_rec_type[THEN to_elim1].
note nat_rec_type2! nat_rec_type1[THEN to_elim1].
note nat_rec_type3! nat_rec_type2[THEN to_elim1].

lemma nat_induction: for x
	if 0: P.[0], suc: ∀x. P.[x] ⟹ x : ℕ ⟹ P.[suc x], [∀x. x : ℕ ⟹ P.[x] : Prop, x : ℕ]
	then P.[x];
	apply nat_induction_axioms[of P, THEN imp_elim1, THEN imp_elim1, THEN all_elim1[of x]];
	by 0 all_intro suc.

lemma nat_cases:
	if 0: x = 0 ⟹ P,
	   suc: ∀x'. x = suc x' ⟹ x' : ℕ ⟹ P, [x : ℕ, P : Prop]
	then P;
	have 1: if [x' : ℕ] then x = x' ⟶ P;
		apply nat_induction[of x'];
		- by 0.
		- for x''; by suc[of x''].
		.
	by 1[of x, THEN imp_elim1].

lemma nat_cases_rule:
	if 0: simp (x = 0) ⟹ P, 1: ∀x'. intro (x' : ℕ) ⟹ simp (x = suc x') ⟹ P, [x : ℕ, P : Prop] then P;
	apply nat_cases[of x];
	- by 0.
	- for x'; by 1[of x'].
	.

obtain nat_case where
	nat_case_type! if A : EQTYPE then nat_case A : A → (ℕ → A) → ℕ → A,
	nat_case_0#simp if A : EQTYPE, z : A, s : ℕ → A then nat_case A z s 0 = z,
	nat_case_suc#simp  if A : EQTYPE, z : A, s : ℕ → A, x : ℕ then nat_case A z s (suc x) = s x;
	- for thesis if assm;
		apply assm[of (fun A : EQTYPE, z : A, s : ℕ → A. nat_rec A z (fun x : ℕ, r : A. s x))].
	.

note nat_case_type1! nat_case_type[THEN to_elim1].
note nat_case_type2! nat_case_type1[THEN to_elim1].
note nat_case_type3! nat_case_type2[THEN to_elim1].

lemma 0_neq_suc: if [x : ℕ] then 0 ≠ suc x;
	apply neq_intro[of ℕ];
	- if 0: 0 = suc x;
		define is0 = nat_case Prop true (fun x : ℕ. false).
		have eq: false = true;
			.. = is0 (suc x); simp is0_def.
			.. = is0 0; simp 0.
			simp is0_def.
		unfold eq.
	by nat_eq_prop.

lemma suc_neq_0: if x! x : ℕ then suc x ≠ 0;
	apply neq_intro[of ℕ];
	- if assm;
		by 0_neq_suc[OF x, THEN neq_imp_false[of ℕ]] assm[dual].
	.

lemma 0_eq_suc_iff_false#simp if x! x : ℕ then 0 = suc x ⟷ false;
	apply 0_neq_suc[OF x, unfold neq_eq, THEN not_imp_iff_false].

lemma suc_eq_0_iff_false#simp if x! x : ℕ then suc x = 0 ⟷ false;
	apply suc_neq_0[OF x, unfold neq_eq, THEN not_imp_iff_false].

lemma 0_eq_suc_elim#elim if 0_s: 0 = suc x, [x : ℕ] then false;
	by 0_s[simp[on (⟷)]].

lemma suc_eq_0_elim#elim if s_0: suc x = 0, [x : ℕ] then false;
	by s_0[simp[on (⟷)]].

obtain funpow where
	funpow_type! if A : EQTYPE then funpow A : (A → A) → ℕ → A → A,
	funpow_0#simp if A : EQTYPE, f : A → A, a : A then funpow A f 0 a = a,
	funpow_suc_left: if A : EQTYPE, f : A → A, n : ℕ, a : A then funpow A f (suc n) a = f (funpow A f n a);
	- for thesis if assm;
		apply assm[of (fun A : EQTYPE, f : A → A, n : ℕ, a : A. nat_rec A a (fun x : ℕ. f) n)].
	.

note funpow_type1! funpow_type[THEN to_elim1].
note funpow_type2! funpow_type1[THEN to_elim1].
note funpow_type3! funpow_type2[THEN to_elim1].

lemma funpow_suc_right: if [A : EQTYPE, f : A → A, n : ℕ, a : A] then funpow A f (suc n) a = funpow A f n (f a);
	apply nat_induction[of n];
	- simp funpow_suc_left.
	- for n' if IH, ... then funpow A f (suc (suc n')) a = funpow A f (suc n') (f a);
		.. = f (funpow A f (suc n') a); simp funpow_suc_left.
		.. = f (funpow A f n' (f a)); simp IH.
		simp funpow_suc_left.
	by eq_prop[of A].

definition 1 = suc 0.

lemma 1_nat! 1 : ℕ; unfold 1_def.

lemma 0_neq_1: 0 ≠ 1; unfold 1_def; apply 0_neq_suc.

obtain (+) where
	add_nat! if x : ℕ, y : ℕ then x + y : ℕ,
	add_0#simp if x : ℕ then x + 0 = x,
	add_suc#simp if x : ℕ, y : ℕ then x + suc y = suc (x + y);
	- for thesis if assm;
		apply assm[of (fun x : ℕ. nat_rec ℕ x (fun z : ℕ. suc))].
	.

lemma 0_add#simp if [x : ℕ] then 0 + x = x;
	apply nat_induction[of x];
	- if #simp 0 + x' = x', ... then 0 + suc x' = suc x'.
	.

lemma suc_add#simp if x: x : ℕ, [y : ℕ] then suc x + y = suc (x + y);
	apply arbitrary[OF x], nat_induction[of y];
	- by nat_eq_prop.
	- for y' if IH, ...;
		by nat_eq_prop #simp IH[THEN all_elim1].
	by nat_eq_prop.

lemma add_1_eq_suc#simp if [x : ℕ] then x + 1 = suc x; simp 1_def.
lemma 1_add_eq_suc#simp if [x : ℕ] then 1 + x = suc x; simp 1_def.

lemma suc_eq_add_1: if [x : ℕ] then suc x = x + 1.

instance add: nat.CommMonoid (+) 0;
	- if [x : ℕ, y : ℕ, z : ℕ] then x + y + z = x + (y + z);
		apply nat_induction[of x];
		- if IH: x' + y + z = x' + (y + z), ...; simp IH.
		by nat_eq_prop.
	- if [x : ℕ, y : ℕ] then x + y = y + x;
		apply nat_induction[of x];
		- if IH: x' + y = y + x', ...; simp IH.
		by nat_eq_prop.
	- if y: y = y', [x : ℕ], ... then x + y = x + y';
		simp y.
	.

obtain (*) where
	mul_nat! if x : ℕ, y : ℕ then x * y : ℕ,
	mul_0#simp if x : ℕ then x * 0 = 0,
	mul_suc#simp if x : ℕ, y : ℕ then x * suc y = x + (x * y);
	- for thesis if assm;
		apply assm[of (fun x : ℕ. nat_rec ℕ 0 (fun z y : ℕ. x + y))].
	.

lemma 0_mul#simp if [x : ℕ] then 0 * x = 0;
	apply nat_induction[of x];
	- if #simp 0 * x' = 0, ...; .
	.

lemma suc_mul#simp if x: x : ℕ, [y : ℕ] then suc x * y = x * y + y;
	apply arbitrary[OF x], nat_induction[of y];
	- for y' if IH, ...;
		by nat_eq_prop #simp IH[THEN all_elim1] add.left_assoc.
	by nat_eq_prop.

instance mul: nat.CommSemiring1 (*) (+) 0 1;
	have left_distrib: if [x : ℕ, y : ℕ, z : ℕ] then x * (y + z) = x * y + x * z;
		apply nat_induction[of x];
		- if #simp x' * (y + z) = x' * y + x' * z, ...
		  then suc x' * (y + z) = suc x' * y + suc x' * z;
			.. = x' * y + (x' * z + y) + z; simp add.left_assoc.
			have 1: x' * z + y = y + x' * z; by add.commute.
			unfold 1;
			simp add.left_assoc.
		by nat_eq_prop.
	- if [x : ℕ, y : ℕ, z : ℕ] then x * y * z = x * (y * z);
		apply nat_induction[of z];
		- if IH: x * y * z' = x * (y * z'), ...;
			simp IH left_distrib.
		by nat_eq_prop.
	- if [x : ℕ, y : ℕ] then x * y = y * x;
		apply nat_induction[of x];
		- if IH: x' * y = y * x', ...; simp IH; unfold[at 0] add.commute.
		by nat_eq_prop.
	- if #simp y = y', [x : ℕ, y : ℕ, y' : ℕ] then x * y = x * y'.
	- if [x : ℕ] then 1 * x = x; simp 1_def.
	.

note#simp mul.left_neutral mul.right_neutral.

lemma insert: if P: P, PQ: P ⟶ Q, [P : Prop, Q : Prop] then Q;
	by PQ[THEN imp_elim1] P.

lemma nat_add_eq_0_imp: if eq: x + y = 0, [x : ℕ, y : ℕ] then x = 0 ∧ y = 0;
	apply and_intro;
	- apply nat_cases[of x];
		-.
		- for x' if #simp, ...; apply eq[simp, THEN suc_eq_0_elim, THEN false_elim].
		.
	- apply nat_cases[of y];
		- for y' if #simp, ...; apply eq[simp, THEN suc_eq_0_elim, THEN false_elim].
		.
	.

lemma nat_0_eq_add_imp: if eq: 0 = x + y, [x : ℕ, y : ℕ] then x = 0 ∧ y = 0;
	apply nat_add_eq_0_imp[OF eq[dual]].

---
### Ordering
---
obtain (≤) where
	le_nat_prop! if x : ℕ, y : ℕ then (x ≤ y) : Prop,
	nat_le_iff_ex_add: if x : ℕ, y : ℕ then x ≤ y ⟷ (∃z : ℕ. y = z + x);
- for thesis if assm;
	apply assm[of (fun x y : ℕ. ∃z : ℕ. y = z + x)].
.

lemma nat_le_imp_ex_add: if xy: x ≤ y, [x : ℕ, y : ℕ] then ∃z : ℕ. y = z + x;
	apply insert[OF xy]; unfold[on (⟷)] nat_le_iff_ex_add.

lemma nat_le_intro_add: for z if eq: y = z + x, [x : ℕ, y : ℕ, z : ℕ] then x ≤ y;
	unfold[on (⟷)] nat_le_iff_ex_add;
	apply ex_intro1[of z], eq.

lemma 0_le_nat! if [y : ℕ] then 0 ≤ y;
	apply nat_le_intro_add[of y].

note#simp 0_le_nat[THEN iff_true].

lemma nat_le_0#simp if [x : ℕ] then x ≤ 0 ⟷ x = 0;
	apply iff_intro;
	- if x0; apply nat_le_imp_ex_add[OF x0 ! !, THEN ex_elim];
		by #elim[guards 2] nat_0_eq_add_imp.
	- if #simp; simp.
	.

lemma suc_le_suc#simp if [x : ℕ, y : ℕ] then suc x ≤ suc y ⟷ x ≤ y;
	apply iff_intro;
	- if suc; apply nat_le_imp_ex_add[OF suc ! !, THEN ex_elim];
		- if 1: suc y = z + suc x, ...;
			apply nat_le_intro_add[of z];
			by 1[simp, THEN suc_inj].
		by nat_eq_prop.
	- if xy; apply nat_le_imp_ex_add[OF xy ! !, THEN ex_elim];
		- if 1: y = z + x, ...;
			apply nat_le_intro_add[of z];
			simp 1.
		.
	.

lemma nat_le_iff_ex_add: if [x : ℕ], y: y : ℕ then x ≤ y ⟷ (∃z : ℕ. y = z + x);
	note! nat_eq_prop.
	apply arbitrary[OF y], nat_induction[of x];
	- apply all_intro;
		- if [y' : ℕ]; apply iff_intro;
			- by ex_intro1[of y'].
			- by 0_le_nat.
			.
		.
	- for x' if IH, ...; apply all_intro;
		- if [y' : ℕ]; apply nat_cases[of y'];
			- if y0: y' = 0;
				simp[on (⟷)] y0;.
			- if y1: y' = suc y'', ...;
				simp[on (⟷)] y1 IH[THEN all_elim1].
			.
		.
	.


lemma nat_le_intro_add: for z if yzx: y = z + x, [x : ℕ, y : ℕ, z : ℕ] then x ≤ y;
	unfold[on (⟷)] nat_le_iff_ex_add;
	apply ex_intro1[of z];
	by #simp yzx.

instance nat_le: TotalOrder ℕ (≤);
	note! nat_eq_prop.
	- if x! x : ℕ, [y : ℕ] then x ≤ y ∨ y ≤ x;
		apply arbitrary[OF x], nat_induction[of y];
		- by or_intro2 0_le_nat.
		- if IH: ∀x : ℕ. x ≤ y' ∨ y' ≤ x, ...;
			apply all_intro;
			- if [x' : ℕ] then x' ≤ suc y' ∨ suc y' ≤ x';
				apply nat_cases[of x'];
				- if #simp; by or_intro1 0_le_nat.
				- if x': x' = suc x'', ...;
					unfold x';
					unfold[on (⟷)] suc_le_suc;
					by IH[THEN all_elim1].
				.
			.
		.
	- if xy: x ≤ y, yz: y ≤ z, ... then x ≤ z;
		apply xy[THEN nat_le_imp_ex_add, THEN ex_elim];
		- if yx: y = yx + x, ...;
			apply yz[THEN nat_le_imp_ex_add, THEN ex_elim];
			- if zy: z = zy + y, ...;
				apply nat_le_intro_add[of (zy + yx)];
				simp yx zy add.left_assoc.
			.
		.
	- if xy: x ≤ y, yx: y ≤ x, !, y! then x = y;
		apply insert[OF xy], insert[OF yx], arbitrary[OF y], nat_induction[of x];
		- apply all_intro;
			- if [y' : ℕ]; simp[on (⟷)]; by #elim eq.sym.
			.
		- for x' if IH, !; apply all_intro;
			- if [y' : ℕ]; apply nat_cases[of y'];
				- if y'_0; simp[on (⟷)] y'_0.
				- if y': y' = suc y'', !;
					simp[on (⟷)] y'; apply IH[THEN all_elim1, OF ! !]>1.
				.
			.
		.
	.

obtain (<) where
	lt_nat: if x : ℕ, y : ℕ then (x < y) : Prop,
	not_lt_0: if x : ℕ then ¬ x < 0, 
	suc_lt: if x : ℕ, y : ℕ then suc x < suc y ⟷ x < y;
- for thesis if assm;
	apply assm[of (fun x y : ℕ. suc x ≤ y)];
	-.
	- if [x : ℕ];
		simp;
		unfold[on (⟷)] nat_le_0;
		fold neq_eq; apply suc_neq_0.
	- if [x : ℕ, y : ℕ];
		simp;
		simp[on (⟷)].
	.
.

---
### Subtraction
---

definition pred = nat_case ℕ 0 (fun p : ℕ. p).

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
		apply assm[of (fun x : ℕ. nat_rec ℕ x (fun _ r : ℕ. pred r))];
		have! (fun _ r : ℕ. pred r) : ℕ → ℕ → ℕ.
		.
	.

lemma 0_diff#simp if [x : ℕ] then 0 ∸ x = 0;
	apply nat_induction[of x];
	- .
	- for x' if IH, ...;
		by #simp IH diff_suc.
	.

lemma suc_diff_suc#simp if x: x : ℕ, [y : ℕ] then suc x ∸ suc y = x ∸ y;
	note! nat_eq_prop.
	apply arbitrary[OF x], nat_induction[of y];
	- apply all_intro;
		- if [x' : ℕ];
			apply nat_induction[of x'];
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

instance add: add.RightCancel (∸);
	- if eq: x = x'; by #simp eq.
	- if x: x : ℕ, [y : ℕ] then x + y ∸ y = x;
		apply arbitrary[OF x], nat_induction[of y];
		-.
		- for y' if IH, ...;
			apply all_intro;
			- if [x' : ℕ] then x' + suc y' ∸ suc y' = x';
				.. = pred (suc x' + y' ∸ y'); simp diff_suc.
				simp IH[THEN all_elim1].
			.
		.
	.

definition _2 = suc 1.
lemma _2_nat! _2 : ℕ; simp _2_def.

---
## Binary Representation

Numeric literals are internally expressed via `_bit0` and `_bit1`.
---

obtain _bit0 where
	_bit0_nat! if x : ℕ then _bit0 x : ℕ,
	_bit0_eq: if x : ℕ then _bit0 x = _2 * x;
	- for thesis if assm;
		apply assm[of (fun x : ℕ. _2 * x)].
	.
obtain _bit1 where
	_bit1_nat! if x : ℕ then _bit1 x : ℕ,
	_bit1_eq: if x : ℕ then _bit1 x = _2 * x + 1; 
	- for thesis if assm;
		apply assm[of (fun x : ℕ. _2 * x + 1)].
	.

lemma _bit1_eq_suc_bit0: if [x : ℕ] then _bit1 x = suc ( _bit0 x); simp _bit1_eq _bit0_eq.

lemma _bit0_add_bit0#simp if [x : ℕ, y : ℕ] then _bit0 x + _bit0 y = _bit0 (x + y);
	simp _bit0_eq mul.left_distrib.

lemma _bit0_add_bit1#simp if [x : ℕ, y : ℕ] then _bit0 x + _bit1 y = _bit1 (x + y);
	simp _bit1_eq_suc_bit0.

lemma _bit1_add_bit0#simp if [x : ℕ, y : ℕ] then _bit1 x + _bit0 y = _bit1 (x + y);
	simp _bit1_eq_suc_bit0.

lemma _bit1_add_bit1#simp if [x : ℕ, y : ℕ] then _bit1 x + _bit1 y = _bit0 (suc (x + y));
	.. = suc (suc ( _bit0 (x + y))); unfold _bit1_eq_suc_bit0.
	simp _bit0_eq _2_def.

lemma suc_bit0#simp if [x : ℕ] then suc ( _bit0 x) = _bit1 x;
	unfold _bit1_eq_suc_bit0.

lemma suc_bit1#simp if [x : ℕ] then suc ( _bit1 x) = _bit0 (suc x);
	simp _bit0_eq _bit1_eq _2_def.


-- The following computation rules are simple but rewrite non-numeral terms.

lemma _bit0_mul: if [x : ℕ, y : ℕ] then _bit0 x * y = _bit0 (x * y);
	simp _bit0_eq mul.left_assoc.

lemma mul_bit0: if [x : ℕ, y : ℕ] then x * _bit0 y = _bit0 (x * y);
	.. = x * _2 * y; simp _bit0_eq mul.left_assoc.
	.. = _2 * x * y; unfold[at 0 1 0 1] mul.commute.
	.. = _2 * (x * y); unfold mul.left_assoc.
	unfold _bit0_eq.

lemma _bit1_mul: if [x : ℕ, y : ℕ] then _bit1 x * y = _bit0 (x * y) + y;
	simp _bit1_eq _bit0_eq mul.left_assoc.

lemma mul_bit1: if [x : ℕ, y : ℕ] then x * _bit1 y = x + _bit0 (x * y);
	simp _bit1_eq_suc_bit0 mul_bit0.

-- The following are restricted
lemma _bit0_mul_bit0#simp if [x : ℕ, y : ℕ] then _bit0 x * _bit0 y = _bit0 ( _bit0 (x * y));
	simp _bit0_mul mul_bit0.

lemma _bit0_mul_bit1#simp if [x : ℕ, y : ℕ] then _bit0 x * _bit1 y = _bit0 (x + _bit0 (x * y));
	simp _bit0_mul mul_bit1.

lemma _bit1_mul_bit0#simp if [x : ℕ, y : ℕ] then _bit1 x * _bit0 y = _bit0 ( _bit0 (x * y) + y);
	simp _bit1_mul mul_bit0.

lemma _bit1_mul_bit1#simp if [x : ℕ, y : ℕ] then _bit1 x * _bit1 y = _bit1 (x + _bit0 (x * y) + y);
	simp _bit1_mul mul_bit1.

lemma suc_1_eq_2#simp suc 1 = 2;
	simp _bit0_eq _2_def.
