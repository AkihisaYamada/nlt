fix (⟺).
assume iff: Magma Prop (⟺).

 and.closed or.closed not.closed iff.closed.

-- `true` is obtained via `false ⟹ false`.
obtain true where true_intro! true, true_type! true ∈ Prop;
	- for thesis if assm;
		apply assm[of (false ⟹ false)].
	.

interpret iff: Magmas (⟺).-- Magma notions wrt (⟺)
