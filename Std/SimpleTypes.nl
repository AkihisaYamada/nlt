---
# Simple (Polymorphic) Type Theory

Church's simple type theory[^Church1940], also known as HOL, considers lambda terms and arrow types.

[^Church1940]
	Alonzo Church. A Formulation of the Simple Theory of Types.
	The Journal of Symbolic Logic, Vol. 5, No. 2. (Jun., 1940), pp. 56-68

We represent the reduction meta-relation by the type-free equality.
Since it is inconvenient to annotate everything with types,
we represent type judgments by the membership meta-relation `:`,
and import the function abstraction without annotation.
---
import Eq, Membership (:), Fun.

---
The arrow types is formalized as follows.
---
fix (→).
assume fun_to#intro if ∀x. x : A ⟹ F.[x] : B then (fun x. F.[x]) : A → B.
assume to_elim1#intro[after 1]#intro[after 2] if f : A → B, x : A then f x : B.

---
We need a dedicated sort `Prop` ($o$ in Church's notation) for propositions. 
---
fix SORT Prop.
assume Prop_type! Prop : SORT.

---
Church then proceeds to declare as primitives negation ($N_{oo}$), disjunction ($A_{ooo}$), and universal quantification ($Π_{o(oα)}$), and axiomatize their classical logical behaviors.
The choice of negation and disjunction as primitives has a (mild) advantage that their behaviors can be characterized by axioms of propositional type, while it is incompatible with intuitionistic logic. Therefore, in this umbrella theory we do not go further.
---

---
Proof assistants based on HOL implement type-synonyms and type-definitions in their kernels.
To achive type synonyms, instead of devising a new machinery, we just let types to have types and allow functions over types.
The following formalization lets us as expressive as possible, while avoiding Girard's Paradox, and avoiding relying numbers whose foundation we are constructing.
---
fix TYPE.
assume TYPE: if A : V then A : TYPE V.
assume to_type! (→) : TYPE V → TYPE V → TYPE V.

begin

---
Type judgment of application can be reduced to that of the function,
if one knows the type of the argument.
---
lemma app_in#intro[after 1] if [x : A, f : A → B] then f x : B.

lemma to_elim: if f: f : A → B, assm: (∀x. x : A ⟹ f x : B) ⟹ Q then Q;
	use f; by assm.

lemma to_TYPE: if [A : TYPE V, B : TYPE V] then A → B : TYPE V.

lemma fun_indep_to#intro if [s : B] then (fun x. s) : A → B.

---
## Basic Combinators

### Identity
---
define id = fun x. x.

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
	.
lemma foo: if x! x : A then (id ∘ id) x = x;
	unfold o_id_app[OF id_type x].

