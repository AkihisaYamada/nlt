---
# (Intuitionistic) Simple Theory of Types

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
### Implication

Church then declares negation ($N_{oo}$), disjunction ($A_{ooo}$), and universal quantification ($Π_{o(oα)}$) as primitive symbols.
The choice of negation and disjunction as primitives is incompatible with intuitionistic logic, and Church anyway admits the rule of inference
> V. From $A_o ⊃ B_o$ and $A_o$, to infer $B_o$.
although implication ($⊃$) is defined from negation and disjunction.

Therefore, we take implication as a primitive.

As we already have implication `⟹` in the foundation, we just assume implication between propositions forms a proposition.
---
assume imp_prop: if p : Prop, q : Prop then (p ⟹ q) : Prop.

---
This is slightly better than
```
assume imp_type: (⟹) : Prop → Prop → Prop.
```
because additional extensionality axioms would interfere the behavior of primitive implication.
Another option is to fully axiomatize new implication like Isabelle/HOL:
```
fix (⟶).
assume imp_type! (⟶) : Prop → Prop → Prop.
assume imp_intro! if p ⟹ q, p : Prop, q : Prop then p ⟶ q.
assume imp_elim: if p ⟶ q, p, p : Prop, q : Prop then q.
```
I think this only introduces indirection, and the same operator can be defined: 
```
definition[as imp] (⟶) = fun p q : Prop. p ⟹ q.
```

### Universal Quantification

Church introduces constant $Π_{o(oα)}$ for every $α$, which we denote by `ALL α`.
---
fix ALL.

assume ALL_type! ALL A : (A → Prop) → Prop.
---
Church's original formulation of ∀-introduction is the rule of inference:
> VI. From $F_{oα} x_α$ to infer $Π_{o(oα)} F_{oα}$ provided that $x_α$ is not a free variable of $F_{oα}$.
---
assume ALL_intro: if f : A → Prop, ∀x. x : A ⟹ f x then ALL A f.
---
The ∀-elimination is the formal axiom (family):
> 5$^α$. $Π_{o(oα)} f_{oα} ⊃ f_{oα} x_α$
---
assume ALL_elim_axiom: if f : A → Prop, x : A then ALL A f ⟹ f x.
---
Church then introduces "notation":
> $[(x_α)A_o] ⟶ Π_{o(oα)} (λx_α A_o)$.
But it is not trivial why this reduction is safe, as parameter α is duplicated.
Types are there to ensure this kind of reduction to terminate, but here α is a type and simple type theory does not consider types like `FUN α : TYPE. (α → Prop) → Prop`.
Formalizing this kind of reduction is in scopes of later research, so we consider that Church implicitly assumed the following notational combinator.
---
fix _BINDER.
assume _BINDER#simp _BINDER op A (x. F.[x]) = op A (fun x : A. F.[x]).

definition[as _all] (∀:) = _BINDER ALL.

---
### Equality

Church defines equality via type-parametric constant:
> $Q_{oαα} ⟶ λx_α λy_α [(f_{oα})[f_{oα} x_α ⊃ f_{oα} y_α]$.
and then introduces polymorphic notation:
> $[A_α = B_α] ⟶ Q_{oαα} A_α B_α$.
Directly following this approach would require something like
```
defintion Q = fun α : TYPE. ...
fix (~).
assume eq_notation: if A : α, B : α then (A ~ B) = Q α A B.
```
However, as we needed syntactic equality already, we instead postulate that equality between terms of the same type is a proposition ($o$).
---
assume eq_prop: if A : TYPE, x : A, y : A then (x = y) : Prop.

---
Church further introduces notation
> $[A_α ≠ B_α] ⟶ [∼(A_α = B_α)]$.
Such notations are safe, because the arguments are not duplicated.
We can achieve this kind of notation by admitting the syntactic composition operator, also known as the combinator B.
---
import Comp.

---
Above assumptions are sufficient to develop intuitionistic fragment of the logic.
---
begin

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
The notation for `≠` is defined using syntactic composition as follows.
---
definition[as neq] (≠) = ((¬) ∘) ∘ (=).

lemma neq_eq: (x ≠ y) = (¬(x = y));
	by #simp neq_def.

---
Church's original treatment of existential quantification is a notation:
> $[(∃x_α)A_o] ⟶ [~[(x_α)[~A_o]]]$.
Directly formalizing this requires adding another assumption (or extending the parser).
Instead, we follow the HOL family for defining a (type-parametric) constant `ex`.
This allows us to reuse the generic binder notation introduced above.
---
definition ex = fun A : TYPE, P : A → Prop. (∀Q : Prop. (∀x : A. P x ⟹ Q) ⟹ Q).

definition[as _ex] (∃:) = _BINDER ex.

---
We show that this theory is an instance of equational, typed, higher-order, impredicative, intuitionistic logic.
---

instance Eq.Prop TYPE.

instance HigherOrder TYPE;
	show!; by to_elim1[OF ALL_type] #simp _all_def.
	show all_intro: if ! ∀ x. x : a ⟹ P.[x];
		by #simp _all_def #intro ALL_intro.
	show all_elim1: for s if all: ∀ x : A. P.[x], ... then P.[s];
		have 1: (fun x : A. P.[x]) s;
			apply ALL_elim_axiom[OF _ _ all[simp _all_def]].
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
The presence of a constant of that type enforces that every type is inhabited.
---
theory SuchSignature :=
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

	instance Inhabited (fun A : TYPE. such x : A. true).

end

theory TypedUniqueSuch :=
	import SuchSignature.
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

theory TypedAnySuch :=
	import SuchSignature.
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
