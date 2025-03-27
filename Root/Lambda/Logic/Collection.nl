base Lambda.Logic.

fix Collect (∈).
assume in_Collect_iff: x ∈ Collect P ⟺ P x.

begin

define[empty_def] ∅ := Collect (λx. false).

define Singleton x := Collect (λy. y = x).

define[cup_def] X ∪ Y := Collect (λx. x ∈ X ∨ x ∈ Y).

setup set_comprehension Collect (λ) ∅ Singleton (∪).

define UNIV := {x. true}.

define[cap_def] X ∩ Y := Collect (λx. x ∈ X ∧ x ∈ Y).

define[ball_def] (∀∈) X α := ∀x. x ∈ X ⟹ α.[x].
define[bex_def] (∃∈) X α := ∃x. x ∈ X ∧ α.[x].

define[subseteq_def] X ⊆ Y := ∀x ∈ X. x ∈ Y.

define[join_def] ⋃ XX := {x. ∃X ∈ XX. x ∈ X}.
define[meet_def] ⋂ XX := {x. ∀X ∈ XX. x ∈ X}.

define[notin_def] x ∉ X := ¬ x ∈ X.

define[has_eq_in] X ∋ x := x ∈ X.

define[image_def] f ` X := {y. ∃x ∈ X. y = f x}.

define[map_def] X → Y := {f. f ` X ⊆ Y}.

lemma in_Singleton_iff: x ∈ {y} ⟺ x = y;
	unfold+ Singleton_def,
	unfold(⟺) in_Collect_iff,
	unfold beta.

lemma in_cup_iff: x ∈ X ∪ Y ⟺ x ∈ X ∨ x ∈ Y;
	unfold cup_def,
	unfold(⟺) in_Collect_iff,
	unfold beta.

lemma in_cap_iff: x ∈ X ∩ Y ⟺ x ∈ X ∧ x ∈ Y;
	unfold cap_def,
	unfold(⟺) in_Collect_iff,
	unfold beta.

lemma ball_intro: (∀x. x ∈ X ⟹ α.[x]) ⟹ ∀x ∈ X. α.[x];
	unfold ball_def.

lemma notin_Collect_iff: x ∉ Collect P ⟺ ¬ P x;
	unfold notin_def,
	unfold(⟺) in_Collect_iff.

lemma Collect_has_iff: Collect P ∋ x ⟺ P x;
	unfold+ has_eq_in,
	unfold(⟺) in_Collect_iff.

lemma in_image_iff: (y ∈ f ` X) ⟺ (∃x ∈ X. y = f x);
	unfold image_def,
	unfold(⟺) in_Collect_iff,
	unfold beta.

----
### The Set of Propositions
----

define Prop := {true, false}.

define Class := Collect ` (UNIV → Prop).

lemma in_Class: X ∈ Class ⟺ (∃P ∈ UNIV → Prop. X = Collect P);
	unfold Class_def,
	unfold(⟺) in_image_iff.

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