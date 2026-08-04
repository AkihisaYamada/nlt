---
# Simple (Polymorphic) Type Theory

This theory formalizes Church's simple type theory[^Church1940] mostly following the original formulation.

[^Church1940]
	Alonzo Church. A Formulation of the Simple Theory of Types.
	The Journal of Symbolic Logic, Vol. 5, No. 2. (Jun., 1940), pp. 56-68

The original theory considers lambda terms with full type annotations.
We take the convention to use type judgement `s : α` instead of annotating every term with its type.
But we follow Church essentially that each bound variable is explicitly typed.
We will use `fun` instead of historical λ.
---
import FunIn, To.

---
We need a dedicated type `Prop` ($o$ in Church's notation) for propositions. 
---
fix Prop.

---
Church then declares as primitives negation ($N_{oo}$), disjunction ($A_{ooo}$), and universal quantification ($Π_{o(oα)}$), and defines implication ($⊃$) from negation and disjunction.
The choice of negation and disjunction as primitives is incompatible with intuitionistic logic, and Church admits the rule of inference
> V. From $A_o ⊃ B_o$ and $A_o$, to infer $B_o$.
although implication is a derived notion.

Therefore, we take implication as a primitive. As we already have implication in the foundation, we just postulate its type.
---
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
assume all_intro: if f : A → Prop, ∀x. x : A ⟹ f x then all f.
---
The ∀-elimination is the formal axiom (family):
> 5$^α$. $Π_{o(oα)} f_{oα} ⊃ f_{oα} x_α$
---
assume all_axiom: if f : A → Prop, x : A then all A f ⟹ f x.
---
Church then introduces "notation":
> $[(x_α)A_o] ⟶ Π_{o(oα)} (λx_α A_o)$.
In our notation, `∀x : α. s` := `all α (fun x : α. s)`, but there are two difficulties to formalize this.

First, as this definition duplicates α, it is not obviously safe to replace the left-hand side to the right-hand side.
Types are there to ensure this kind of replacement to terminate, but here α is a type and simple type theory does not consider types of types.
One can argue that any such reduction is safe, provided the right-hand side has a type.
So we postulate such an abstraction, where `(fun x. F.[x]) s` can be reduced to `F.[s]`, provided the latter is typed.

The next question is how `∀x : α. F.[x]` should be internally. One clean option would be `(∀:) α F`, but now the above argument fails because `(∀:) α` cannot be represented as a typed term.
We conclude that `(∀:)` should take the two arguments simultaneously, i.e., `(∀:)(α, x. s)`. This demands syntactic pairing.
---

begin

definition (∀:) := fun (A,P). all A (fun x : A. P.[x]).

---
Similarly, Church's treatment of existential quantification as a notation
> $[(∃x_α)A_o] ⟶ [~[(x_α)[~A_o]]]$.
uses untyped arguments. 
---
definition (∃:) := fun (A,P). ∀Q : Prop. (∀x : A. P.[x] ⟹ Q) ⟹ Q.

---
The type-parametrized equality
> $Q_{oαα} ⟶ λx_α λy_α [(f_{oα})[f_{oα} x_α ⊃ f_{oα} y_α]$.
also takes a type as a parameter.
---
definition eq := fun A. fun x y : A. ∀f : A → Prop. f x ⟹ f y.



lemma to_TYPE: if [A : TYPE V, B : TYPE V] then A → B : TYPE V.

lemma all_prop#intro if [f : A → Prop] then all A f : Prop;
	by to_elim1[OF all_type].

lemma all_elim1:
	if all: all A (fun x : A. F.[x]), F: ∀x. x : A ⟹ F.[x] : Prop, x: x : A
	then F.[x];
	apply funIn_app_elim[of(z. z), OF _ x];
	apply all_axiom[OF _ x all];
	apply fun_to;
	by #elim F.

interpretation Propositional (:).

definition false := ∀x : Prop. x.
definition true := (false ⟹ false).
definition[as not] (¬) := fun P : Prop. P ⟹ false. 
definition[as and] (∧) := fun P Q : Prop. ∀R : Prop. (P ⟹ Q ⟹ R) ⟹ R.
definition[as iff] (⟺) := fun P Q : Prop. (P ⟹ Q) ∧ (Q ⟹ P).
definition[as or] (∨) := fun P Q : Prop. ∀R : Prop. (P ⟹ R) ⟹ (Q ⟹ R) ⟹ R.

interpretation False;
	- by #simp false_def.
	- if false: false, P: P : Prop then P;
		apply all_elim1[OF false[unfold false_def]];
		by P.
	.

interpretation True;
	by #simp true_def.

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

