import! Std.Iff.

begin

instance Iff.Eq;
	show: x = y ⟺ (∀P. P.[x] ⟹ P.[y]);
		apply iff_intro;
		- if eq, Px: P.[x];
			by eq_cong_meta[of P, OF eq, THEN eq_imp, OF Px].
		- if assm; by assm[of (z. x = z)].
		.
	.
