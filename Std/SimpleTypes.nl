---
# Simple Typed Lambda Calculus

This theory formalizes simply typed lambda calculus.

[^Church1940]
	Alonzo Church. A Formulation of the Simple Theory of Types.
	The Journal of Symbolic Logic, Vol. 5, No. 2. (Jun., 1940), pp. 56-68

Church originally considered lambda terms with full type annotations.
We take the later convention to use type judgement `s : α` instead of annotating every term with its type,
but explicitly assign types when variables are bound.
We will use `fun` instead of historical "λ".

A fundamental design choice is how to treat reductions. The original paper does not formulate reduction relation but admit rule of inference:

> II. To replace any part $((λx_β M_α)N_β)$ of a formula by the result of substituting 
$N_β$ for $x_β$ throughout $M_α$, provided that the bound variables of $M_α$ are distinct both 
from $x_β$ and from the free variables of $N_β$.

While we can formalize reduction as "replacement" (see Std/Membership/Fun), Church also uses $⟶$ to represent notational equality. It is also possible to understand that his $⟶$ is something the parser must be able perform, but I would like such an operation to be achieved in the formalized part.

Therefore, we import syntactic equality, and postulate type-restricted β-reduction.
---

import Eq, Membership (:), FunTo (fun_:).

---
Church does not introduce a formal notation for $α$	being a type. We will use `α : TYPE` following Martin-Löf.
This choice makes this theory stronger than the original, as type abstraction `fun α : TYPE. F.[α]` is permitted.
It also allows type synonyms. 

---
fix TYPE.

assume to_type! if A : TYPE, B : TYPE then A → B : TYPE.

begin

---
Most foundations on simple type theory require every type to be inhabited, and there is a polymorphic way to denote a witness.
---
theory Inhabited :=
	fix inhabitant.
	assume inhabitant_type! if A : TYPE then inhabitant A : A.
end

