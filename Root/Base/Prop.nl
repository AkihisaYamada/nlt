---
## Proposition as a Class
---

import Class.
fix PROP.

assume imp_type! P ∈ PROP ⟹ Q ∈ PROP ⟹ (P ⟹ Q) ∈ PROP.

begin

theory Relation:
	fix A (≤).
	import Binary (≤) A A PROP.
begin
	interpret BinRel.
end

theory Order:
	import Relation.
	import Transitive.
end

theory Preorder:
	import Order.
	import Reflexive.
end

theory PartialEquivalence:
	import Order.
	import Symmetric.
end

theory Equivalence:
	import Preorder.
	import Tolerance.
end

theory BoundedAll:
	fix (∀:).
	assume all_type! (∀x. x ∈ A ⟹ α.[x] ∈ PROP) ⟹ (∀x ∈ A. α.[x]) ∈ PROP.
	assume all_intro: (∀x. x ∈ A ⟹ α.[x]) ⟹ (∀x. x ∈ A ⟹ α.[x] ∈ PROP) ⟹ ∀x:A. α.[x].
	assume all_elim1: for x, (∀y:A. α.[y]) ⟹ x ∈ A ⟹ (∀y. y ∈ A ⟹ α.[y] ∈ PROP) ⟹ α.[x].
begin
	lemma all_elim:
		if all: ∀x:ι. α.[x]
		then ∀P. ((∀x. x: ι ⟹ α.[x]) ⟹ P) ⟹ (∀y. y ∈ ι ⟹ α.[y] ∈ PROP) ⟹ P;
		for P if assm, !;
			apply assm;
			for x if !;
				apply all_elim1[OF all, of x].
			.
		.
	obtain true where true_type! true ∈ PROP, true_intro! true;
		for thesis if assm;
			apply assm[of (∀P:PROP. P ⟹ P)];
			by all_intro.
		.
end
