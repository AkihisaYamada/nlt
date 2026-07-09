import Magmas.

fix Prop (∧) (∨) (¬) (⟺) (∀∈) (∃∈).

import imp: Magma Prop (⟹).
import and: Magma Prop (∧).
import or: Magma Prop (∨).
import not: Unary (¬) Prop Prop.
import iff: Magma Prop (⟺).
assume allIn_type! if ∀x. x ∈ A ⟹ P.[x] ∈ Prop then (∀x ∈ A. P.[x]) ∈ Prop.
assume exIn_type!  if ∀x. x ∈ A ⟹ P.[x] ∈ Prop then (∃x ∈ A. P.[x]) ∈ Prop.

begin

theory Minimal :=
	interpret Propositional;
		obtain false where false_type! false ∈ Prop;-- One can obtain false.
			- for thesis if assm;
				apply assm[of (∀P ∈ Prop. P)].
			.
		.
	import Propositional.Minimal.
begin

end

theory Intuitionistic :=
	interpret Propositional;
		obtain false where -- One can obtain false.
			false_type! false ∈ Prop,
			false_elim: false ⟹ ∀P. P ∈ Prop ⟹ P;
			- for thesis if assm;
				apply assm[of (∀P ∈ Prop. P)].
			.
		.
	import Propositional.Intuitionistic.
begin
	interpret FreeOrder.Minimal.
end

theory Classical :=
	import Intuitionistic.
	import ExcludedMiddle.
begin
	interpret FreeOrder.Intuitionistic.
end
ctxt.
