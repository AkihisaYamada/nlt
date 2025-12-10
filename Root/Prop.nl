fix (∈) PROP.
assume imp_type! P ∈ PROP ⟹ Q ∈ PROP ⟹ (P ⟹ Q) ∈ PROP.

begin

interpret Classes.

theory Relation:
	fix A (≤).
	import Binary (≤) A A PROP.
begin
	note! closed.
end

theory Preorder:
	import ..Preorder.
	import Relation.
end

theory Tolerance:
	import ..Tolerance.
	import Relation A (=).
end

theory PartialEquivalence:
	import ..PartialEquivalence.
	import Relation A (=).
end

theory Equivalence:
	import ..Equivalence.
	import Relation A (=).
begin
	interpret Tolerance.
	interpret PartialEquivalence.
end



