---
# Propositions

We fix a class `Prop` in which logical operators are closed.
---
import Prop.

fix true false (∧) (∨) (¬) (⟺).
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

interpret iff: Magmas (⟺).-- Magma notions wrt (⟺)
