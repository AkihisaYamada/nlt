base Root.

import Lambda.

fix nat (0) suc rec.

import zero: Member nat 0.
import suc: Unary suc nat nat.

assume suc_inj: suc x = suc y ⟹ nat x ⟹ nat y ⟹ x = y.

assume induct: P 0 ⟹ (∀x. P x ⟹ nat x ⟹ P (suc x)) ⟹ ∀x. nat x ⟹ P x.
assume rec_zero: rec z s 0 = z.
assume rec_suc: nat x ⟹ rec z s (suc x) = s x (rec z s x).

begin

setup rewrite eq_prop1 eq_prop2 eq.refl eq.trans.
setup dual eq.sym.

setup define beta.

note! zero.type.
note! suc.type.

lemma induction:
	if 0: α.[0], suc: ∀x. α.[x] ⟹ nat x ⟹ α.[suc x] then ∀x. nat x ⟹ α.[x];
	define P x := α.[x].
	have z': P 0;
		unfold(=) P_def,
		apply 0.
	have suc': for x, P x ⟹ nat x ⟹ P (suc x);
		unfold(=) P_def,
		apply suc(x)=.
	- for x;
		apply induct(P)[OF z' suc'](x)[unfolded(=) P_def]=.
	.

lemma induction_rule:
	if xt: nat x, 0: α.[0], suc: ∀x. α.[x] ⟹ nat x ⟹ α.[suc x] then α.[x];
	by induction[OF 0 suc xt].

obtain (+) where
	zero_add: nat x ⟹ 0 + x = x,
	suc_add: nat x ⟹ nat y ⟹ suc x + y = suc (x + y);
	- for thesis, if assm:;
		apply assm(λx y. rec y (λx' z. suc z) x),
		by #unfold(=)+ beta rec_zero rec_suc.
	.

interpret add: Monoid nat (+);
	show! for x y, if xt: nat x, !nat y then nat (x + y);
		apply induction_rule[OF xt](x. nat (x + y)),
		by #unfold(=) zero_add suc_add.
	show: for x y z, if xt: nat x, ! nat y, ! nat z then x + y + z = x + (y + z);
		apply induction_rule[OF xt](x. x + y + z = x + (y + z)),
		- by #unfold(=) zero_add.
		- for x', if IH: x' + y + z = x' + (y + z), ! nat x';
			by #unfold(=) suc_add IH.
		.
	show: for x, if ! nat x then 0 + x = x;
		by #unfold(=) zero_add.
	show: ∀x. nat x ⟹ x + 0 = x;
		apply induction!2,
		- by #unfold(=) zero_add.
		- for x, if IH: x + 0 = x, !nat x;
			by #unfold(=) suc_add IH.
		.
	.

lemma add_suc: ∀x y. nat x ⟹ nat y ⟹ x + suc y = suc (x + y);
	have 1: for y, if ! nat y then ∀x. nat x ⟹ x + suc y = suc (x + y);
		apply induction!2,
		- by #unfold(=) zero_add.
		- for x, if IH:, ! ;
			by #unfold(=) suc_add IH.
		.
	by 1.

obtain case where
	case_zero: case z s 0 = z,
	case_suc: ∀z s x. nat x ⟹ case z s (suc x) = s x;
	- for thesis, if assm:;
		apply assm(λz s. rec z (λx r. s x)),
		by #unfold(=) rec_zero rec_suc beta.
	.

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
	- for thesis, if assm: ;
		apply assm(λx. rec x (λ _ r. pred r)),
		by #unfold(=)+ beta rec_zero rec_suc.
	.

lemma zero_diff: ∀x. nat x ⟹ 0 ∸ x = 0;
	apply induction!2,
	- by #unfold(=) diff_zero.
	- for x, if IH:, !;
		by #unfold(=) diff_suc IH pred_zero.
	.

lemma suc_diff_suc: ∀x y. nat x ⟹ nat y ⟹ suc x ∸ suc y = x ∸ y;
	have 1: for x, if ! nat x then ∀y. nat y ⟹ suc x ∸ suc y = x ∸ y;
		apply induction!2,
		- by #unfold(=) diff_suc diff_zero pred_suc.
		- for y, if IH:, !;
			unfold(=) diff_suc,
			unfold(=) IH.
		.
	by 1.
