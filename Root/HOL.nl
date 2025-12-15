---
# Higher-Order Logic

Higher-order logic (HOL) allows quantification over arbitrary functions.
In other words, it is SOL where the classes for individuals and quantifiable are the same.
---

import SOL;
	instantiate IND := QTYPE.
	.

begin

theory Choice:
	fix CHOICE.
	assume choice:
		if ∀x ∈ A. ∃y ∈ B. P x y, A ∈ QTYPE, B ∈ CHOICE
		then ∃f ∈ A → B. ∀x ∈ A. P x (f x).
end
