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

import Eq.
import type? Membership (:), FunTo (fun_:) (⇒).

---
Church does not introduce a formal notation for $α$	being a type. We will use `α : TYPE` following Martin-Löf.
This design choice allows type abstraction `fun α : TYPE. F.[α]` and thus type synonyms,
which Church informally uses for the notation `α'` to denote `(αα)(αα)`, or `(α ⇒ α) ⇒ α ⇒ α` in modern notation.
---
fix TYPE.

assume to_type! if A : TYPE, B : TYPE then A ⇒ B : TYPE.

begin

---
Most foundations on simple type theory require every type to be inhabited, and there is a polymorphic way to denote a witness. It is `undefined` in Isabelle/HOL but here we follow a more explanatory naming following Coq.
---
theory Inhabited :=
	fix inhabitant.
	assume inhabitant_type! if A : TYPE then inhabitant A : A.
end

---
Type-theory-based proof assistants implement functionalities to infer type parameters from
the type of an argument.
---
binder IMPLICIT 51 0.
syntax[level 51] IMPLICIT _ : _. _ := IMPLICIT_:.

theory ImplicitArg :=
	fix IMPLICIT_:.
	assume IMPLICIT: for 'A Arg if a : Arg.['A], 'A : ARG then (IMPLICIT 'X : ARG. Arg.['X]) f a = f 'A a.
begin
	---
	This functionality allows us to denote *the* type of a term, so a term cannot have multiple types essentially.
	---
	obtain typeof where typeof: if x : 'a, 'a : TYPE then typeof x = 'a;
		- for thesis if assm;
			apply assm[of ((IMPLICIT 'a : TYPE. 'a) (fun 'a : TYPE, x : 'a. 'a))];
			- if [x : 'a, 'a : TYPE]; simp IMPLICIT[of 'a].
			.
		.

end
