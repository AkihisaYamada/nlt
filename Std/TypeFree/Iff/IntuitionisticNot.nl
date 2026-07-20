
fix (¬).
assume not_iff: ¬P ⟺ (P ⟹ false).

begin

interpret Not.

interpret Not.IntuitionisticNot;
	by #simp not_iff false_iff.

interpret MinimalNot.

context ClassicalNot begin

	interpret Iff.IntuitionisticNot;
		by iff_intro not_intro #elim not_elim.

end
