import Membership.

fix Prop (∧) (∨) (¬) (⟺) (∀∈) (∃∈).

import imp: Magma Prop (⟹).
import and: Magma Prop (∧).
import or: Magma Prop (∨).
import not: Unary (¬) Prop Prop.
import iff: Magma Prop (⟺).
assume allIn_type! if ∀x. x ∈ A ⟹ P.[x] ∈ Prop then (∀x ∈ A. P.[x]) ∈ Prop.
assume exIn_type!  if ∀x. x ∈ A ⟹ P.[x] ∈ Prop then (∃x ∈ A. P.[x]) ∈ Prop.

begin

interpret Propositional;
	obtain false where ! false ∈ Prop;-- One can obtain false.
		- for thesis if assm;
			apply assm[of (∀P ∈ Prop. P)].
		.
	.

theory Minimal:
	import Minimal.
	import in: AllExRel (∈) (∀∈) (∃∈).
begin

end

theory Intuitionistic:
	import .Minimal.
	import Intuitionistic.
begin
end

theory Classical:
	import .Intuitionistic.
	import Classical.
begin
end
