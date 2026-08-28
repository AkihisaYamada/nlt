import! Std.Iff.

begin

lemma iff_app_cong#cong? if f: f = f', x: x = x' then f x ⟺ f' x';
	simp[on (=)] f x.

instance Iff.Eq;
	show: x = y ⟺ (∀P. P.[x] ⟹ P.[y]);
		apply iff_intro;
		- if eq, Px: P.[x];
			by eq_cong_meta[of P, OF eq, THEN eq_imp, OF Px].
		- if assm; by assm[of (z. x = z)].
		.
	.
