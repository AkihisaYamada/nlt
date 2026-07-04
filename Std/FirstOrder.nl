import Membership.

fix Prop QTYPE (∧) (∨) (¬) (⟺) (∀∈) (∃∈) false.

import Propositional.

assume allIn_type! if A ∈ QTYPE, ∀x. x ∈ A ⟹ P.[x] ∈ Prop then (∀x ∈ A. P.[x]) ∈ Prop.
assume exIn_type! if A ∈ QTYPE, ∀x. x ∈ A ⟹ P.[x] ∈ Prop then (∃x ∈ A. P.[x]) ∈ Prop.

begin
