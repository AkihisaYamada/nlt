---
# Type-Free Natural Numbers

This theory formalizes natural numbers in naive logic.

## Axiomatization

We use `fun` to allow for deriving addition etc.
---
import Eq, Membership, FunIn.

fix ℕ 0 suc rec.

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
assume induction: if x ∈ ℕ, P.[0], ∀x. P.[x] ⟹ x ∈ ℕ ⟹ P.[suc x] then P.[x].

---
### Type-Free Recursor

The following two recursor equations should look natural:
---
assume rec_zero#simp rec z s 0 = z.
assume rec_suc#simp if x ∈ ℕ then rec z s (suc x) = s x (rec z s x).
---
However, note that they impose no type on the first two arguments.
A polymorphism version would demand `z ∈ T` and `∀x. x ∈ T ⟹ s x ∈ T` (or `s ∈ T → T`),
and a dependent-type version would demand
`z ∈ T 0` and
`∀n. n ∈ ℕ ⟹ ∀x. x ∈ T n ⟹ s x ∈ T (suc n)` (or `s ∈ FUN n ∈ ℕ. T n → T(suc n)`),
with a notion of type-family.
---

begin

note! zero.closed.
note! suc.closed.

instance Magmas (=) (∈).

instance nat: Equivalence ℕ (=);
	- .
	- by #elim eq.sym.
	- by #intro[after 2] eq.trans.
	.

obtain (+) where
	zero_add#simp if x ∈ ℕ then 0 + x = x,
	suc_add#simp if x ∈ ℕ, y ∈ ℕ then suc x + y = suc (x + y);
	- for thesis if assm;
		define[as add] (+) = fun x y ∈ ℕ. rec y (fun z ∈ ℕ. suc) x.
		apply assm[of (+)];
		- if ! x ∈ ℕ;
			by #simp add_def.
		- if ! x ∈ ℕ, ! y ∈ ℕ;
			by #simp add_def. 
		.
	.

lemma add_zero#simp if x: x ∈ ℕ then x + 0 = x;
	apply induction[OF x];
	- if IH: x' + 0 = x', ... then suc x' + 0 = suc x';
		.. = suc (x' + 0).
		unfold IH.
	.

lemma add_suc#simp if x: x ∈ ℕ then ∀y. y ∈ ℕ ⟹ x + suc y = suc (x + y);
	apply induction[OF x];
	-.
	- for x' if IH, ! if ! y ∈ ℕ then suc x' + suc y = suc (suc x' + y);
		.. = suc (x' + suc y).
		.. = suc (suc (x' + y)); unfold IH.
		.
	.

---
Addition over natural numbers forms a commutative monoid.
The interesting part is the inductive proof of `x + y ∈ ℕ`; if one restricts the induction principle to propositions, then one would require type assumptions on `rec`.
---
instance add: nat.CommMonoid (+) 0;
	- show! if x: x ∈ ℕ, !y ∈ ℕ then x + y ∈ ℕ;
		apply induction[OF x].
	- if x: x ∈ ℕ, ! y ∈ ℕ then x + y = y + x;
		apply induction[OF x];
		- if IH: x' + y = y + x', ... then suc x' + y = y + suc x';
			.. = suc (x' + y).
			.. = suc (y + x'); unfold IH.
			.
		.
	- if x: x ∈ ℕ, ! y ∈ ℕ, ! z ∈ ℕ then x + y + z = x + (y + z);
		apply induction[OF x];
		- by #simp zero_add.
		- for x' if IH: x' + y + z = x' + (y + z), ...;
			by #simp suc_add IH.
		.
	.

obtain case where
	case_zero: case z s 0 = z,
	case_suc: if x ∈ ℕ then case z s (suc x) = s x;
	- for thesis, if assm;
		apply assm(fun z s. rec z (fun x r. s x));
		by #unfold(=) rec_zero rec_suc beta.
	.

definition[as one] 1 = suc 0.

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
