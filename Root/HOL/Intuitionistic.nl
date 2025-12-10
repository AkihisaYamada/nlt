obtain false where false_type! false ∈ PROP, false_elim: false ⟹ ∀P. P ∈ PROP ⟹ P;
	for thesis if assm;
		apply assm[of (∀P ∈ PROP. P)];
		by #elim all_elim.
	.

import ..Intuitionistic.

begin

interpret Minimal.
