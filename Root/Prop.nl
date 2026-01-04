import Membership.

fix Prop.

namespace imp:
	import Magma Prop (⟹).
end

begin

note! imp.closed.


theory Relation:
	fix A (≤).
	import Binary (≤) A A Prop.
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
