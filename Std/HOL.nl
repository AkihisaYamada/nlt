---
# (Intuitionistic) Higher-Order Logic

Based on the simply typed lambda calculus, this theory formalizes Church's foundation of logic[^Church1940] with some deviations.

[^Church1940]
	Alonzo Church. A Formulation of the Simple Theory of Types.
	The Journal of Symbolic Logic, Vol. 5, No. 2. (Jun., 1940), pp. 56-68
---
import SimpleTypes.

---
## Axiomatization

Church declares types $ι$ for individuals and $o$ for propositions.
We introduce `Prop` for $o$, while individuals are left unspecified.
---
fix Prop.
assume prop_type! Prop : TYPE.

---
### Equality

Church defines equality via type-parametric constant $Q$:
> $Q_{oαα} ⟶ λx_α λy_α [(f_{oα})[f_{oα} x_α ⊃ f_{oα} y_α]$.
where $⊃$ denotes implication, and then introduces polymorphic notation:
> $[A_α = B_α] ⟶ Q_{oαα} A_α B_α$.

It is possible to rigorously follow this approach (we will admit polymorphic notation anyway).
However, as we needed syntactic equality already, we instead postulate that equality between terms of the same type is a proposition ($o$).
---
assume eq_prop: if 'a : TYPE, x : 'a, y : 'a then (x = y) : Prop.

---
Church further introduces notation
> $[A_α ≠ B_α] ⟶ [~(A_α = B_α)]$.
Such notations could be considered justified because the arguments are not duplicated.
Therefore, we admit some syntactic combinators that does not duplicate arguments.
---
import Syntactic.

---
### Implication

Church then declares negation ($N_{oo}$), disjunction ($A_{ooo}$), and universal quantification ($Π_{o(oα)}$) as primitive symbols.
The choice of negation and disjunction as primitives is incompatible with intuitionistic logic, and Church anyway admits the rule of inference
> V. From $A_o ⊃ B_o$ and $A_o$, to infer $B_o$.
although implication ($⊃$) is defined from negation and disjunction.

Therefore, we take implication as a primitive.

While we already have implication `⟹` in the foundation,
we follow Isabelle/HOL to introduce a new implication symbol:
---
fix (⟶).
assume imp_type! (⟶) : Prop ⇒ Prop ⇒ Prop.
assume imp_intro! if P ⟹ Q, P : Prop, Q : Prop then P ⟶ Q.
assume imp_elim1: if P ⟶ Q, P, P : Prop, Q : Prop then Q.

---
This indirection makes proving cumbersome, compared to reusing the native implication:
```
assume imp_prop: if p : Prop, q : Prop then (p ⟹ q) : Prop.
```
The latter design would be fine with Church's original formulation. On the other hand, HOL[^Gordon1988]
requires implication to return either `true` or `false`, and therefore makes structural analysis of formulas impossible.

[^Gordon1988]
	Michael JC Gordon. HOL: A proof generating system for higher-order logic.
	VLSI specification, verification and synthesis. 1988. 73-128.




### Universal Quantification

Church introduces constant $Π_{o(oα)}$ for every $α$, which we denote by `all_ α`.
---
fix all_.

assume all__type! all_ 'a : ('a ⇒ Prop) ⇒ Prop.
---
Church's original formulation of ∀-introduction is the rule of inference:
> VI. From $F_{oα} x_α$ to infer $Π_{o(oα)} F_{oα}$ provided that $x_α$ is not a free variable of $F_{oα}$.
---
assume all__intro: if ∀x. x : 'a ⟹ f x, f : 'a ⇒ Prop then _all 'a f.
---
The ∀-elimination is the formal axiom (family):
> 5$^α$. $Π_{o(oα)} f_{oα} ⊃ f_{oα} x_α$
---
assume all__elim_axiom: if f : 'a ⇒ Prop, x : 'a then _all 'a f ⟶ f x.
---
Church then introduces "notation":
> $[(x_α)A_o] ⟶ Π_{o(oα)} (λx_α A_o)$.
But it is not trivial why this reduction is safe, as parameter α is duplicated.
Types are there to ensure this kind of reduction to terminate, but here α is a type and simple type theory does not consider types like `FUN α : TYPE. (α ⇒ Prop) ⇒ Prop`.
Instead, we first formalize implicit type parameters to be able to define a symbol `all` such that `all f = all_ α f` if `f : α ⇒ Prop`.
---
import ImplicitArg.

import Comp.

---
Above assumptions are sufficient to develop intuitionistic fragment of Church's foundation of logic.
---
begin

definition[as _all] (∀:) = ((IMPLICIT 'a : TYPE. 'a ⇒ Prop) all_ ∘) ∘ (fun_:).

lemma all_def:
	if ['a : TYPE, ∀x. x : 'a ⟹ F.[x] : Prop]
	then (∀x : 'a. F.[x]) = all_ 'a (fun x : 'a. F.[x]);
	simp _all_def IMPLICIT[of 'a].

note imp_type1! imp_type[THEN to_elim1].
note imp_type2! imp_type1[THEN to_elim1].

instance Prop TYPE Prop (:) (⇒).




---
## Defining Logical Operators

Logical operators that do not require type parameters can be defined as simply typed constants.
---

definition false = ∀x : Prop. x.
definition true = (false ⟶ false).
definition[as not] (¬) = (fun P : Prop. P ⟶ false). 
definition[as and] (∧) = (fun P Q : Prop. ∀R : Prop. (P ⟶ Q ⟶ R) ⟶ R).
definition[as iff] (⟷) = (fun P Q : Prop. (P ⟶ Q) ∧ (Q ⟶ P)).
definition[as or] (∨) = (fun P Q : Prop. ∀R : Prop. (P ⟶ R) ⟶ (Q ⟶ R) ⟶ R).

---
The notation for `≠` is defined using syntactic composition as follows.
---
definition[as neq] (≠) = ((¬) ∘) ∘ (=).

lemma neq_eq: (x ≠ y) = (¬(x = y));
	by #simp neq_def.

---
Church's original treatment of existential quantification is a notation:
> $[(∃x_α)A_o] ⟶ [~[(x_α)[~A_o]]]$.
Directly formalizing this requires adding another assumption (or extending the parser).
Instead, we follow the HOL family for defining a (type-parametric) constant `ex_`.
This allows us to reuse the generic binder notation introduced above.
---
definition ex_ = (fun 'a : TYPE, P : 'a ⇒ Prop. (∀Q : Prop. (∀x : 'a. P x ⟶ Q) ⟶ Q)).

definition[as _ex] (∃:) = ((IMPLICIT 'a : TYPE. 'a ⇒ Prop) ex_ ∘) ∘ (fun_:).

lemma ex_def:
	if ['a : TYPE, ∀x. x : 'a ⟹ P.[x] : Prop]
	then (∃x : 'a. P.[x]) = (∀Q : Prop. (∀x : 'a. (fun y : 'a. P.[y]) x ⟶ Q) ⟶ Q);
	simp _ex_def IMPLICIT[of 'a] ex__def.

---
We show that this theory is an instance of equational, typed, higher-order, impredicative, intuitionistic logic.
---

instance HigherOrder TYPE;
	show!; by to_elim1[OF all__type] #simp all_def.
	show all_intro: if [∀ x. x : 'a ⟹ P.[x]], ...;
		simp all_def; apply all__intro.
	show all_elim1: for s if all: ∀x : 'a. P.[x], ... then P.[s];
		have 1: (fun x : 'a. P.[x]) s;
			apply all__elim_axiom[THEN imp_elim1, OF _ _ all[simp all_def]];
			by all__type[THEN to_elim1].
		use 1; simp.
	note #simp ex_def.
	- .
	- for x if Px: P.[x] for 'a if ...;
		simp;
		apply all_intro;
		- if [Q : Prop]; apply imp_intro;
			- if all; apply all[THEN all_elim1, of x, OF ! ! !, THEN imp_elim1]; by Px.
			.
		.
	- if ex: ∃x : 'a. P.[x] for Q if assm, ...;
		apply ex[simp, THEN all_elim1, of Q, OF ! ! !, THEN imp_elim1];
		apply all_intro;
		- if !x : 'a;
			by assm[of x].
		.
	.

instance Impredicative;
	note#cong eq_cong_meta.
	retain false;
		- for P; simp false_def.
		.
	.

instance Intuitionistic;
	note#simp not_def true_def.
	interpret Imp.
	interpret Not, IntuitionisticNot;
		- if nP: ¬P, P, ... for Q if ...;
			apply nP[simp, THEN imp_elim1, OF P, THEN false_elim].
		.
	interpret And;
		- by #simp and_def.
		- if [P, Q], ... then P ∧ Q;
			simp and_def; apply all_intro;
			- if [R : Prop]; apply imp_intro;
				- if PQR: P ⟶ Q ⟶ R then R;
					apply PQR[THEN imp_elim1, THEN imp_elim1].
				.
			.
		- if and: P ∧ Q, ...;
			apply and[simp and_def, THEN all_elim1[of P], THEN imp_elim1].
		- if and: P ∧ Q, ...;
			apply and[simp and_def, THEN all_elim1[of Q], THEN imp_elim1]. 
		.
	interpret? Iff;
		- by #simp iff_def.
		- by #simp iff_def.
		- if PQ: P ⟷ Q, ...;
			apply PQ[simp iff_def, THEN and_elim1, THEN imp_elim1].
		- if PQ: P ⟷ Q, ...;
			apply PQ[simp iff_def, THEN and_elim2, THEN imp_elim1].
		.
	interpret Or;
		note #simp or_def.
		-.
		- if [Q] for P if ...; simp; apply all_intro;
			- if [R : Prop]; apply imp_intro;
				- if PR?; apply imp_intro; .
				.
			.
		- if PQ: P ∨ Q, PR: P ⟹ R, QR: Q ⟹ R, ...;
			apply PQ[simp, THEN all_elim1[of R], THEN imp_elim1, THEN imp_elim1];
			use PR QR.
		.
	.

instance Quantifiable TYPE.

---
Church's original formulation does not assume propositions are **equal to** either true or false. Gordon's HOL assumes this on its propositional type `bool`, while Isabelle/HOL splits `prop` and two-valued `bool`.
Here we will just define a predicate when a proposition is two valued.
---
definition two_valued = (fun p : Prop. p = true ∨ p = false).

lemma two_valued_type! two_valued : Prop ⇒ Prop;
	by eq_prop[of Prop] #simp two_valued_def.

note two_valued_type1! two_valued_type[THEN to_elim1].

lemma two_valued_true! two_valued true;
	by or_intro1 eq_prop[of Prop] #simp two_valued_def.
lemma two_valued_false! two_valued false;
	by or_intro2 eq_prop[of Prop] #simp two_valued_def.

---
A predicate represents a "set" when the result is two valued for any input. With extensionality, sets are identified by its members.
---
definition is_set_ = (fun 'a : TYPE, p : 'a ⇒ Prop. ∀x : 'a. two_valued (p x)).

definition is_set = (IMPLICIT 'a : TYPE. 'a ⇒ Prop) is_set_ .

lemma is_set__type: if ['a : TYPE] then is_set_ 'a : ('a ⇒ Prop) ⇒ Prop;
	simp is_set__def.

lemma is_set_fun_imp_two_valued:
	if 1: is_set (fun x : 'a. P.[x]), ['a : TYPE, ∀x. x : 'a ⟹ P.[x] : Prop, x : 'a]
	then two_valued P.[x];
	apply 1[simp is_set_def IMPLICIT[of 'a] is_set__def, THEN all_elim1[of x], simp].

lemma is_set_fun_intro:
	if 1: ∀x. x : 'a ⟹ two_valued P.[x], ['a : TYPE, ∀x. x : 'a ⟹ P.[x] : Prop]
	then is_set (fun x : 'a. P.[x]);
	by 1 #simp is_set_def IMPLICIT[of 'a] is_set__def.

---
It is also convenient to have the unique existence notation.
---
definition ex1_ = (fun 'a : TYPE, P : 'a ⇒ Prop.
	∀Q : Prop. ∀x : 'a. P x ⟶ (∀y : 'a. P y ⟶ y = x) ⟶ Q
).

definition[as _ex1] (∃!:) = ((IMPLICIT 'a : TYPE. 'a ⇒ Prop) ex1_ ∘) ∘ (fun_:).

lemma ex1_def:
	if ['a : TYPE, ∀x. x : 'a ⟹ P.[x] : Prop]
	then (∃!x : 'a. P.[x]) = ex1_ 'a (fun x : 'a. P.[x]);
	simp _ex1_def IMPLICIT[of 'a].


---
## Additional Postulates
---

---
Church introduces a family of constants $ι_{α(oα)}$, which is used to denote both
the unique choice operator and Hilbert's choice operator $ε$.
We denote `SUCH α : (α ⇒ Prop) ⇒ α` instead of $ι_{α(oα)}$.
The presence of a constant of that type enforces that every type is inhabited. So we should restrict `α` to be a type.
---
theory SuchSignature :=
	fix SUCH.
	assume SUCH_type: if 'a : TYPE then SUCH 'a : ('a ⇒ Prop) ⇒ 'a.
begin

	definition (such_:) = ((IMPLICIT 'a : TYPE. 'a ⇒ Prop) SUCH ∘) ∘ (fun_:).

	lemma such_def:
		if ['a : TYPE, ∀x. x : 'a ⟹ P.[x] : Prop]
		then (such x : 'a. P.[x]) = SUCH 'a (fun x : 'a. P.[x]);
		simp such_:_def IMPLICIT[of 'a].

	lemma SUCH_app_type! if ['a : TYPE, f : 'a ⇒ Prop] then SUCH 'a f : 'a;
		by SUCH_type[THEN to_elim1].

	lemma such_type! if ['a : TYPE, ∀x. x : 'a ⟹ P.[x] : Prop] then (such x : 'a. P.[x]) : 'a;
		unfold such_def.

	instance Inhabited (fun 'a : TYPE. such x : 'a. true).

end
