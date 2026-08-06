---
# Simple (Polymorphic) Type Theory

This theory formalizes Church's simple type theory[^Church1940] mostly following the original formulation.

[^Church1940]
	Alonzo Church. A Formulation of the Simple Theory of Types.
	The Journal of Symbolic Logic, Vol. 5, No. 2. (Jun., 1940), pp. 56-68

The original theory considers lambda terms with full type annotations.
We take the convention to use type judgement `s : α` instead of annotating every term with its type,
but essentially follow Church by explicitly assigning a type to each bound variable.
We will use `fun` instead of historical λ.

A fundamental design choice is how to treat reductions. The 1940 paper does not formulate reduction relation but admit rule of inference:

> II. To replace any part $((λx_β M_α)N_β)$ of a formula by the result of substituting 
$N_β$ for $x_β$ throughout $M_α$, provided that the bound variables of $M_α$ are distinct both 
from $x_β$ and from the free variables of $N_β$.

While we can formalize reduction as "replacement" (see Std/Membership/Fun), Church also uses $⟶$ to represent notational equality. It is also possible to understand that his $⟶$ is something the parser must perform, but I would like such an operation to be achieved in the formalized part.

Therefore, we import syntactic equality, and formalize β-reduction as a type-restricted equation.
---
import Eq, FunIn, To.

---
Church then declares a special type $o$, `Prop` in our notation, for propositions,
and declares negation ($N_{oo}$), disjunction ($A_{ooo}$), and universal quantification ($Π_{o(oα)}$) as primitive symbols.
The choice of negation and disjunction as primitives is incompatible with intuitionistic logic, and Church admits the rule of inference
> V. From $A_o ⊃ B_o$ and $A_o$, to infer $B_o$.
although implication ($⊃$) is defined from negation and disjunction.

Therefore, we take implication as a primitive.
As we already have implication in the foundation, we just postulate its type.
---
fix Prop.
assume imp_type! (⟹) : Prop → Prop → Prop.

---
Now we axiomatize universal quantification.
Church introduces constant $Π_{o(oα)}$ for every $α$.
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

It is not trivial that this reduction is safe, as parameter α is duplicated.
Types are there to ensure this kind of reduction to terminate, but here α is a type and simple type theory does not consider types of types.
A formalized machinery for this kind of reduction is rather involving, so we treat Church's "notation" involving type paremeters as assumptions.
---
fix (∀:).
syntax ∀ _ : _. _ := ∀:.
assume all_def: (∀x : A. P.[x]) = all A (fun x : A. P.[x]).

---
Church treats existential quantification just a notation:
> $[(∃x_α)A_o] ⟶ [~[(x_α)[~A_o]]]$.
We adopt this treatment, with an intuitionist-friendly definition.
---
fix (∃:). syntax ∃ _ : _. _ := ∃:.
assume ex_def: (∃x : A. P.[x]) = (∀Q : Prop. (∀x : A. P.[x] ⟹ Q) ⟹ Q).

---
Church defines equality via type-parametrized equality constant
> $Q_{oαα} ⟶ λx_α λy_α [(f_{oα})[f_{oα} x_α ⊃ f_{oα} y_α]$.
> $[A_α = B_α] ⟶ Q_{oαα} A_α B_α$.
As we needed syntactic equality already, I see little sense in defining such type-parametrized equality. We just postulate that equality between terms of the same type is a prosition ($o$).
---
assume eq_prop: if x : A, y : A then (x = y) : Prop.

begin

---
Other logical constants do not require type parameters and thus can be defined as simply typed constants.
---

definition false = ∀x : Prop. x.
definition true = (false ⟹ false).
definition[as not] (¬) = fun P : Prop. P ⟹ false. 
definition[as and] (∧) = fun P Q : Prop. ∀R : Prop. (P ⟹ Q ⟹ R) ⟹ R.
definition[as iff] (⟺) = fun P Q : Prop. (P ⟹ Q) ∧ (Q ⟹ P).
definition[as or] (∨) = fun P Q : Prop. ∀R : Prop. (P ⟹ R) ⟹ (Q ⟹ R) ⟹ R.

interpret Typed (:) .

interpret AllRelStrict (:) (∀:);
	- by to_elim1[OF all_type] #simp all_def.
	- if ! ∀ x. x : a ⟹ P.[x];
		by #simp all_def #intro all_rule.
	- for s if all: ∀ x : A. P.[x], ... then P.[s];
		have 1: (fun x : A. P.[x]) s;
			apply all_axiom[OF _ _ all[unfold all_def]].
		use 1; simp.
	.

note#intro all_intro.
note#elim all_elim.

interpret Intuitionistic;
	interpret False;
		- by #simp false_def.
		- if false: false for P if ...;
			apply all_elim1[OF false[unfold false_def]].
		retain true;
			by #simp true_def.
		.
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
	interpret Iff;
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
			by all_elim1[OF PQ[simp] !][OF ! PR QR].
		.
	.

interpret ExRelStrict (:) (∃:);
	note #simp ex_def.
	- if Px: P.[x] for A if ...;
		simp;
		apply all_intro;
		- if ! Q : Prop, all;
			by all_elim1[OF all !, OF ! Px].
		.
	- if ex: ∃x : A. P.[x] for Q if assm, ...;
		apply ex[simp, THEN all_elim1, of Q, OF ! !];
		apply all_intro;
		- for x if ...;
			by assm[of x].
		.
	.

---
## Basic Combinators

### Identity
---
definition id = fun x. x.

lemma id_type! id : A → A;
	unfold id_def.

lemma id_eq#simp[after 1] if x! x : A then id x = x;
	unfold id_def;
	apply fun_app_eq[OF _ x].


---
### Constant Function
---
define const = fun x y. x.

lemma const_type! const : A → B → A;
	unfold const_def.

lemma const_app#simp[after 1] if [x : A] then const x y = x;
	unfold const_def;
	unfold fun_app[of (A → A)];
	unfold fun_app[of A].

---
### Function Composition
---
define[as o] (∘) = fun f g x. f (g x).

lemma o_type! (∘) : (C → B) → (A → C) → A → B;
	unfold o_def.

lemma o_eq: if [f : C → B, g : A → C] then f ∘ g = fun x. f (g x);
	have 1: (∘) f = fun g x. f (g x);
		unfold o_def;
		apply fun_app[of ((A → C) → A → B)].
	unfold 1;
	apply fun_app[of (A → B)].

lemma o_app: if f! f : C → B, g! g : A → C, [x : A] then (f ∘ g) x = f (g x);
	unfold o_eq[OF f g];
	apply fun_app[of B].

lemma o_id_app: if f! f : A → B, x! x : A then (f ∘ id) x = f x;
	... = f (id x); apply o_app[OF f _ x].
	.
lemma id_o_app: if f! f : A → B, x! x : A then (id ∘ f) x = f x;
	... = id (f x); apply o_app[OF id_type f x].
	note! f[THEN to_elim1, OF x].
	.
lemma foo: if x! x : A then (id ∘ id) x = x;
	unfold o_id_app[OF id_type x].

