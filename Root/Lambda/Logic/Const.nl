base Logic.

-----
## Constructor
-----

import UniqueChoice.

fix Const is_const.
assume Const_is_const: is_const Const.
assume Const_neq_app: is_const c ⟹ Const ≠ c x.
assume const_app: is_const c ⟹ is_const (c x).
assume const_app_eq_app: is_const c ⟹ is_const d ⟹ c x = d y ⟹ c = d ∧ x = y.

begin

define const_arg v := THE x. ∃c. is_const c ∧ v = c x.

lemma const_arg: if c: is_const c then const_arg (c x) = x;
	unfold const_arg_def,
	apply ex1_imp_THE_eq,
	apply ex1_intro(x),
	apply ex_intro1(c),
	apply and_intro,
	- by c.
	- .
	- for y, if ex: ∃c'. is_const c' ∧ c x = c' y then x = y;
		obtain c' where c': is_const c', cc': c x = c' y;
			- for P;
				note 1: ex[unfolded ex_def].
				note 2: 1[unfolded(⟺) and_imp_iff].
				apply 2=.
			.
		note and: const_app_eq_app[OF c c' cc'].
		by and_elim2[OF and].
	have! ∃c'. is_const c' ∧ c x = c' x;
		apply ex_intro1(c),
		apply and_intro,
		by c.
	.

----
### Collections
----

define Collect := Const true.

lemma Collect_is_const: is_const Collect;
	unfold Collect_def,
	apply const_app,
	by Const_is_const.

lemma const_arg_Collect: const_arg (Collect P) = P;
	by const_arg[OF Collect_is_const].

define[in_def] x ∈ X := (λ) (const_arg X) x.

interpret Collection;
	show: x ∈ Collect P ⟺ P.[x];
		unfold in_def,
		unfold const_arg_Collect.
	.

thm in_un_iff.

setup set_comprehension ∅ Singleton Collect (∪).

define UNIV := {x. true}.

define[meet_def] ⋂ XX := {x. ∀X. X ∈ XX ⟹ x ∈ X}.

----
### The Set of Propositions
----

define Prop := {true, false}.

define[subset_def] X ⊆ Y := ∀x. x ∈ X ⟹ x ∈ Y.

infix ` 100 100 100.
define[image_def] f ` X := {y. ∃x. x ∈ X ∧ y = f x}.

infix → 61 60 60.
define[map_def] X → Y := {f. f ` X ⊆ Y}.

lemma in_image: (y ∈ f ` X) = (∃x. x ∈ X ∧ y = f x);
	unfold+ image_def in_Collect beta.

define Class := Collect ` (UNIV → Prop).

lemma in_Class: (X ∈ Class) = (∃p. p ∈ UNIV → Prop ∧ X = Collect p);
	unfold+ Class_def in_image.




define Russel := {X. X ∉ X}.

--- Needs two-valued
lemma MEET_in_Class: if XX: XX ⊆ Class then ⋂ XX ∈ Class;
	have 1: ⋂ XX = {x. ∀X. X ∈ XX ⟹ x ∈ X};
		by MEET_def.
	have prop: for x, (∀X. X ∈ XX ⟹ x ∈ X) ∈ Prop;
		
	show prop: ∀x. prop ((λx. ∀X. X ∈ XX ⟹ x ∈ X) x).
	show pred: pred (λx. ∀X. X ∈ XX ⟹ x ∈ X).
		by pred.intro[OF prop].
	show 1: ∃p. pred p ∧ ⋂ XX = Collect p.
		sorry.
	sorry.
---

define 0 := Const false.
define Suc := Const 0.

define Nat := ⋂ {X. 0 ∈ X ∧ Suc ` X ⊆ X}.

