---
## Proposition as a Class
---

import Class.
fix PROP.

assume imp_type! P ∈ PROP ⟹ Q ∈ PROP ⟹ (P ⟹ Q) ∈ PROP.

begin

interpret imp: Magma PROP (⟹).

theory Relation:
	fix A (≤).
	import Binary (≤) A A PROP.
end

theory BoundedAll:
	fix (∀∋).
	assume all_type! (∀x. x ∈ A ⟹ P.[x] ∈ PROP) ⟹ (∀x ∈ A. P.[x]) ∈ PROP.
	assume all_intro: (∀x. x ∈ A ⟹ P.[x]) ⟹ (∀x. x ∈ A ⟹ P.[x] ∈ PROP) ⟹ ∀x ∈ A. P.[x].
	assume all_elim1: for x, (∀y ∈ A. P.[y]) ⟹ x ∈ A ⟹ (∀y. y ∈ A ⟹ P.[y] ∈ PROP) ⟹ α.[x].
begin
	lemma all_elim:
		if all: ∀x ∈ A. P.[x]
		then ∀thesis. ((∀x. x ∈ A ⟹ P.[x]) ⟹ thesis) ⟹ (∀y. y ∈ A ⟹ P.[y] ∈ PROP) ⟹ thesis;
		for thesis if assm, !;
			apply assm;
			for x if !;
				apply all_elim1[OF all, of x].
			.
		.
	obtain true where true_type! true ∈ PROP, true_intro! true;
		for thesis if assm;
			apply assm[of (∀P ∈ PROP. P ⟹ P)];
			by all_intro.
		.
end
