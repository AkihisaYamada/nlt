import Std, Eq, Prop, Nat.
begin

theorem 2_mul_nat_eq: if x_is_nat: x : ℕ then 2 * x = x + x;
	apply nat_induction[of x];
	-.
	- for y if IH: 2 * y = y + y, y_is_nat: y : ℕ then 2 * suc y = suc y + suc y;
		note! y_is_nat.
		unfold mul_suc;
		unfold IH; .
	- by nat_eq_prop.
	- apply x_is_nat.
	.
thm nat_eq_prop.