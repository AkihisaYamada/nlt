---
# Propositions

We fix a class `Prop` in which logical operators are closed.
---
import Prop.

fix false (∧) (∨) (¬) (⟺).
assume false_type! false ∈ Prop.
import and: Magma Prop (∧).
import or: Magma Prop (∨).
import not: Unary (¬) Prop Prop.
import iff: Magma Prop (⟺).

begin

note! imp.closed and.closed or.closed not.closed iff.closed.

-- `true` is obtained via `false ⟹ false`.
obtain true where true_intro! true, true_type! true ∈ Prop;
	- for thesis if assm;
		apply assm[of (false ⟹ false)].
	.

interpret iff: MetaRelation (⟺).-- Magma notions wrt (⟺)


extend Iff begin

	interpret Prop_iff: Equivalence Prop (⟺);
		-.
		- if xy: x ⟺ y; by iff.sym[OF xy].
		- if xy: x ⟺ y, yz: y ⟺ z; by iff.trans[OF xy yz].
		.

end

theory TypeSafeMinimal :=
	import base? ..TypeSafeMinimal.
	import base.Membership.
begin

	interpret .Iff.

	extend base? base.MetaRelation begin
		interpret? Iff.MetaRelation.
	end

	interpret Prop_and: Prop_iff.CommMonoid (∧) true;
		by and.commute and.left_assoc.

end
