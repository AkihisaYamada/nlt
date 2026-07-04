---
# Type-Free Natural Numbers

This theory formalizes natural numbers in naive logic.

## Axiomatization

We use `fun` to allow for deriving addition etc.
---
import Fun.

fix ℕ (0) suc rec.

-- Zero is a natural number (`0 ∈ ℕ`).
import zero: Member 0 ℕ.

-- The natural numbers are closed under successors (`x ∈ ℕ ⟹ suc x ∈ ℕ`).
import suc: Unary suc ℕ ℕ.

-- Successor is injective in ℕ
assume suc_inj: if suc x = suc y, x ∈ ℕ, y ∈ ℕ then x = y.

---
### Induction Principle

We assume a type-free form of the induction principle.
Note that a propositional form would require `∀x. x ∈ ℕ ⟹ P.[x] ∈ Prop`,
and would not allow inductively deriving type judgements.
---
assume induction: if P.[0], ∀x. P.[x] ⟹ x ∈ ℕ ⟹ P.[suc x], x ∈ ℕ then P.[x].

---
### Recursor

The following two recursor equations should look natural:
---
assume rec_zero: rec z s 0 = z.
assume rec_suc: if x ∈ ℕ then rec z s (suc x) = s x (rec z s x).
---
However, note that they impose no type on the first two arguments.
A polymorphic form would demand `z ∈ T` and `∀x. x ∈ T ⟹ s x ∈ T` (or `s ∈ T → T`),
and a dependently typed form would demand `z ∈ T 0` and `∀n. n ∈ ℕ ⟹ ∀x. x ∈ T n ⟹ s x ∈ T (suc n)`
(or `s ∈ Πn ∈ ℕ. T n → T(suc n)`).
---

begin

note! zero.closed.
note! suc.closed.

interpret Equivalence ℕ (=);
	- .
	- by #intro[after 1] eq.sym.
	- by #intro[after 2] eq.trans.
	.

obtain (+) where
	zero_add: if x ∈ ℕ then 0 + x = x,
	suc_add: if x ∈ ℕ, y ∈ ℕ then suc x + y = suc (x + y);
	- for thesis if assm;
		apply assm[of (fun x y. rec y (fun z. suc) x)];
		- for f if !;
			apply assm[of f];
			by #unfold rec_zero rec_suc.
		.
	.

interpret add: CommMonoid (+) 0;
	show! if xt: x ∈ ℕ, !y ∈ ℕ then x + y ∈ ℕ;
		apply induction_rule[OF xt, of (x. x + y ∈ ℕ)];
		by #unfold zero_add suc_add.
	- if xt: x ∈ ℕ, ! y ∈ ℕ, ! z ∈ ℕ then x + y + z = x + (y + z);
		apply induction_rule[OF xt, of (x. x + y + z = x + (y + z))];
		- by #unfold zero_add.
		- for x' if IH: x' + y + z = x' + (y + z), ! nat x';
			by #unfold suc_add IH.
		.
	- if ! nat x then 0 + x = x;
		by #unfold(=) zero_add.
	show: ∀x. nat x ⟹ x + 0 = x;
		apply induction!2,
		- by #unfold(=) zero_add.
		- for x, if IH: x + 0 = x, !nat x;
			by #unfold(=) suc_add IH.
		.
	.

lemma add_suc: ∀x y. nat x ⟹ nat y ⟹ x + suc y = suc (x + y);
	have! for y, if ! nat y then ∀x. nat x ⟹ x + suc y = suc (x + y);
		apply induction!2,
		- by #unfold(=) zero_add.
		- for x, if IH, !;
			by #unfold(=) suc_add IH.
		.
	.

obtain case where
	case_zero: case z s 0 = z,
	case_suc: ∀z s x. nat x ⟹ case z s (suc x) = s x;
	- for thesis, if assm;
		apply assm(λz s. rec z (λx r. s x));
		by #unfold(=) rec_zero rec_suc beta.
	.

define 1 := suc 0.

lemma zero_eq_one_elim: if eq: 0 = 1
then 
	

define pred := case 0 (λp. p).

lemma pred_zero: pred 0 = 0;
	by #unfold(=) pred_def case_zero.

lemma pred_suc: if !nat x then pred (suc x) = x;
	by #unfold(=) pred_def case_suc beta.

symbol ∸.
infix ∸ 100 101 100.

obtain (∸) where
	diff_zero: nat x ⟹ x ∸ 0 = x,
	diff_suc: nat x ⟹ nat y ⟹ x ∸ suc y = pred (x ∸ y);
	- for thesis, if assm;
		apply assm(λx. rec x (λ _ r. pred r)),
		by #unfold(=)+ beta rec_zero rec_suc.
	.

lemma zero_diff: ∀x. nat x ⟹ 0 ∸ x = 0;
	apply induction!2,
	- by #unfold(=) diff_zero.
	- for x, if IH, !;
		by #unfold(=) diff_suc IH pred_zero.
	.

lemma suc_diff_suc: ∀x y. nat x ⟹ nat y ⟹ suc x ∸ suc y = x ∸ y;
	have 1: for x, if ! nat x then ∀y. nat y ⟹ suc x ∸ suc y = x ∸ y;
		apply induction!2,
		- by #unfold(=) diff_suc diff_zero pred_suc.
		- for y, if IH, !;
			unfold(=) diff_suc,
			unfold(=) IH.
		.
	by 1.
