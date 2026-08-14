---
# Simple (Intuitionistic) Type Theory

This theory formalizes Church's simple type theory[^Church1940] with some deviations.

[^Church1940]
	Alonzo Church. A Formulation of the Simple Theory of Types.
	The Journal of Symbolic Logic, Vol. 5, No. 2. (Jun., 1940), pp. 56-68

The original theory considers lambda terms with full type annotations.
We take the convention to use type judgement `s : α` instead of annotating every term with its type,
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
Types are $ι$ for individuals, $o$ for propositions, and $αβ$ for functions returning $α$ from $β$.
Here introduce `Prop` for $o$ and denote `β → α` for $αβ$, while individuals are left unspecified.
Church does not introduce a formal notation for $α$	being a type.
We will use `α : TYPE` following Martin-Löf. This choice makes this theory stronger than the original, as type abstraction `fun α : TYPE. F.[α]` is permitted.
---
fix TYPE Prop.
assume prop_type! Prop : TYPE.
assume to_type! if A : TYPE, B : TYPE then A → B : TYPE.

---
Church then declares negation ($N_{oo}$), disjunction ($A_{ooo}$), and universal quantification ($Π_{o(oα)}$) as primitive symbols.
The choice of negation and disjunction as primitives is incompatible with intuitionistic logic, and Church admits the rule of inference
> V. From $A_o ⊃ B_o$ and $A_o$, to infer $B_o$.
although implication ($⊃$) is defined from negation and disjunction.

Therefore, we take implication as a primitive.
As we already have implication in the foundation, we just postulate its type.
---
assume imp_type! (⟹) : Prop → Prop → Prop.

---
To formalize universal quantification, Church introduces constant $Π_{o(oα)}$ for every $α$.
We denote this constant by `all α`.
---
fix all.
assume all_type! all A : (A → Prop) → Prop.
---
Church's original formulation of ∀-introduction is the rule of inference:
> VI. From $F_{oα} x_α$ to infer $Π_{o(oα)} F_{oα}$ provided that $x_α$ is not a free variable of $F_{oα}$.
---
assume all_rule: if f : A → Prop, ∀x. x : A ⟹ f x then all A f.
---
The ∀-elimination is the formal axiom (family):
> 5$^α$. $Π_{o(oα)} f_{oα} ⊃ f_{oα} x_α$
---
assume all_axiom: if f : A → Prop, x : A then all A f ⟹ f x.
---
Church then introduces "notation":
> $[(x_α)A_o] ⟶ Π_{o(oα)} (λx_α A_o)$.
But it is not trivial why this reduction is safe, as parameter α is duplicated.
Types are there to ensure this kind of reduction to terminate, but here α is a type and simple type theory does not consider types like `FUN α : TYPE. (α → Prop) → Prop`.
Formalizing this kind of reduction is in scopes of later research, so we consider that Church implicitly assumed the following notational combinator.
---
fix _BINDER.
assume _BINDER#simp _BINDER op A (x. F.[x]) = op A (fun x : A. F.[x]).

definition[as _all] (∀:) = _BINDER all.

---
Church defines equality via type-parametric constant
> $Q_{oαα} ⟶ λx_α λy_α [(f_{oα})[f_{oα} x_α ⊃ f_{oα} y_α]$.
> $[A_α = B_α] ⟶ Q_{oαα} A_α B_α$.
As we needed syntactic equality already, we just postulate that equality between terms of the same type is a proposition ($o$).
---
assume eq_type! if A : TYPE then (=) : A → A → Prop.

---
Church further introduces notation
> $[A_α ≠ B_α] ⟶ [∼(A_α = B_α)]$.
This notation is safe, because the arguments are not duplicated.
We can achieve this kind of notation by admitting the syntactic composition operator, also known as the combinator B.
---
import Comp.

---
Above assumptions are sufficient to develop intuitionistic fragment of the logic.
---
begin

note! imp_type[THEN to_elim1, THEN to_elim1].

lemma eq_app_type! if [A : TYPE, x : A] then (x =) : A → Prop;
	by eq_type[of A, THEN to_elim1].

lemma eq_prop#intro[after 1] if [A : TYPE, x : A, y : A] then (x = y) : Prop;
	by eq_app_type[of A, THEN to_elim1].

---
## Defining Logical Operators

Logical operators that do not require type parameters can be defined as simply typed constants.
---

definition false = ∀x : Prop. x.
definition true = (false ⟹ false).
definition[as not] (¬) = fun P : Prop. P ⟹ false. 
definition[as and] (∧) = fun P Q : Prop. ∀R : Prop. (P ⟹ Q ⟹ R) ⟹ R.
definition[as iff] (⟺) = fun P Q : Prop. (P ⟹ Q) ∧ (Q ⟹ P).
definition[as or] (∨) = fun P Q : Prop. ∀R : Prop. (P ⟹ R) ⟹ (Q ⟹ R) ⟹ R.

---
Church's original treatment of existential quantification is a notation:
> $[(∃x_α)A_o] ⟶ [~[(x_α)[~A_o]]]$.
Directly formalizing this requires adding another assumption (or extending the parser).
Instead, we follow the HOL family for defining a (polymorphic) constant `ex`.
This allows us to reuse the generic binder notation introduced above.
---
definition ex = fun A : TYPE, P : A → Prop. (∀Q : Prop. (∀x : A. P x ⟹ Q) ⟹ Q).

definition[as _ex] (∃:) = _BINDER ex.

---
The notation for `≠` is defined using syntactic composition as follows.
---
definition[as neq] (≠) = ((¬) ∘) ∘ (=).

lemma neq_eq: (x ≠ y) = (¬(x = y));
	by #simp neq_def.


---
We show that this theory is an instance of equational, typed, higher-order, impredicative, intuitionistic logic.
---

instance Eq.Prop TYPE.

instance HigherOrder TYPE;
	show!; by to_elim1[OF all_type] #simp _all_def.
	show all_intro: if ! ∀ x. x : a ⟹ P.[x];
		by #simp _all_def #intro all_rule.
	show all_elim1: for s if all: ∀ x : A. P.[x], ... then P.[s];
		have 1: (fun x : A. P.[x]) s;
			apply all_axiom[OF _ _ all[simp _all_def]].
		use 1; simp.
	note #simp _ex_def ex_def.
	- for x if Px: P.[x] for A if ...;
		simp;
		apply all_intro;
		- if ! Q : Prop, all;
			apply all_elim1[OF all !, of x]; by Px.
		.
	- if ex: ∃x : A. P.[x] for Q if assm, ...;
		apply ex[simp, THEN all_elim1, of Q, OF ! !];
		apply all_intro;
		- if !x : A;
			by assm[of x].
		.
	.

instance Impredicative;
	note#cong eq_cong_meta.
	retain false;
		- for P; simp false_def.
		.
	retain true;
		simp true_def false_def.
	.

instance Intuitionistic;
	note#simp not_def.
	interpret Not, IntuitionisticNot;
		- if nP: ¬P, P, ... for Q if ...;
			apply nP[simp, OF P, THEN false_elim].
		.
	interpret And;
		note#simp and_def.
		- if and: P ∧ Q, ...; use and.
		- if and: P ∧ Q, ...; use and.
		.
	interpret? Iff;
		- by #simp iff_def.
		- by #simp iff_def.
		- if PQ: P ⟺ Q, ...;
			by PQ[simp iff_def, THEN and_elim1].
		- if PQ: P ⟺ Q, ...;
			by PQ[simp iff_def, THEN and_elim2].
		.
	interpret Or;
		note #simp or_def.
		- if PQ: P ∨ Q, PR: P ⟹ R, QR: Q ⟹ R, ...;
			by all_elim1[OF PQ[simp] !][OF ! ! PR QR].
		.
	.
instance Iff.Quantifiable TYPE.

---
It is also convenient to have the unique existence notation.
---
definition ex1 = fun A : TYPE, P : A → Prop.
	∀Q : Prop. ∀x : A. P x ⟹ (∀y : A. P y ⟹ y = x) ⟹ Q.

definition[as _ex1] (∃!:) = _BINDER ex1.


---
## Additional Postulates
---

theory Classical :=
	assume nnot_elim_axiom: ∀P : Prop. ¬ ¬P ⟹ P.
begin

	instance Prop.Classical;
		- if nnP: ¬ ¬ P, ... then P;
			apply nnot_elim_axiom[THEN all_elim1[of P]]; by nnP.
		.

end

---
Church introduces a family of constants $ι_{α(oα)}$, which is used to denote "the" term satisfying the given predicate, or as Hilbert's $ε$-operator. We denote `SUCH α : (α → Prop) → α` for $ι_{α(oα)}$.
The presence of a constant of that type forces that every type is nonempty.
---
theory SuchType :=
	fix SUCH.
	assume SUCH_type: if A : TYPE then SUCH A : (A → Prop) → A.
begin

	definition (such_:) = _BINDER SUCH.

	lemma such_def: (such x : A. P.[x]) = SUCH A (fun x : A. P.[x]);
		simp such_:_def.

	lemma SUCH_app_type! if [A : TYPE, f : A → Prop] then SUCH A f : A;
		by SUCH_type[THEN to_elim1].

	lemma such_type! if [A : TYPE, ∀x. x : A ⟹ P.[x] : Prop] then (such x : A. P.[x]) : A;
		unfold such_def.

end

theory UniqueChoice :=
	import SuchType.
	assume unique_such_axiom: if A : TYPE then
		∀P : A → Prop. ∀x : A. P x ⟹ (∀y : A. P y ⟹ x = y) ⟹ P (SUCH A P).
begin

	instance TypedThe (such_:);
		note#cong eq_cong_meta.
		- for x if Px: P.[x], uniq: ∀y. P.[y] ⟹ y : A ⟹ x = y, ... then P.[such z : A. P.[z]];
			define f = (fun z : A. P.[z]).
			have fS: f (SUCH A f);
				apply unique_such_axiom[of A, THEN all_elim1[of f], THEN all_elim1[of x]];
				by Px uniq #simp f_def.
			by fS[simp f_def] #simp such_def.
		.

end

theory Choice :=
	import SuchType.
	assume such_axiom: if A : TYPE then ∀P : A → Prop. ∀x : A. P x ⟹ P (SUCH A P).
begin

	instance TypedSome TYPE (such_:);
		note#cong eq_cong_meta.
		- for x if Px: P.[x] for A if ...;
			define f = (fun z : A. P.[z]).
			have fS: f (SUCH A f);
				apply such_axiom[of A, THEN all_elim1[of f], THEN all_elim1[of x]];
				by Px #simp f_def.
			by fS[simp f_def] #simp such_def.
		.

end
