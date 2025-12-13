import Base.

fix (∈) PROP.
assume imp_type! P ∈ PROP ⟹ Q ∈ PROP ⟹ (P ⟹ Q) ∈ PROP.

begin

interpret Membership.

theory Relation:
	fix A (≤).
	import Binary (≤) A A PROP.
begin
	note! closed.
end

theory Preorder:
	import Preorder.
	import Relation.
end

theory Tolerance:
	import Tolerance.
	import Relation A (=).
end

theory PartialEquivalence:
	import PartialEquivalence.
	import Relation A (=).
end

theory Equivalence:
	import Equivalence.
	import Relation A (=).
begin
	interpret Tolerance.
	interpret PartialEquivalence.
end

---
## Equational Propositional Logic

In equational propositional logic, one only compares terms of the same type.
Such types are collected in `EQTYPE`.
---
theory Eq:
	fix EQTYPE (=).
	assume eq_prop: if A ∈ EQTYPE then ∀x y. x ∈ A ⟹ y ∈ A ⟹ (x = y) ∈ PROP.
	assume eq_refl: if A ∈ EQTYPE then ∀x. x ∈ A ⟹ x = x.
	assume eq_imp: for P A if A ∈ EQTYPE, x = y, P.[x], x ∈ A, y ∈ A, (∀z. z ∈ A ⟹ P.[z] ∈ PROP) then P.[y].
begin

	interpret Membership.

	lemma eq_trans:
		if A! A ∈ EQTYPE, xy: x = y, yz: y = z, !x ∈ A, !y ∈ A, !z ∈ A then x = z;
		apply eq_imp[of (w. x = w) A, OF A yz xy];
		by eq_prop[OF A].

end

