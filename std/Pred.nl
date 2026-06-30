---
# Predicate Logics

Predicates allow propositions to be built from predicate (relation) symbols applied to terms of ``individual'' types.
We only specify the function type constructor `→` in order to specify how to build propositions.
---

import Prop.
import Fun.

begin

---
An example predicate logic is equational logic.
It permits equations between terms of the same type to be proposition,
provided the type belongs to a class called `EQTYPE`.
---
theory Eq:
	import Eq.
	fix EQTYPE.
	assume eq_fun_type: if A ∈ EQTYPE then (=) ∈ A → A → PROP.
end


