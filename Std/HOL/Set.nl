---
# HOL Set
---
import Quotients.

begin

definition set_eq_ = (fun 'a : TYPE, p q : 'a ⇒ Prop. ∀x : 'a. p x ⟷ q x).

lemma set_eq__type!
	if ['a : TYPE] then set_eq_ 'a : ('a ⇒ Prop) ⇒ ('a ⇒ Prop) ⇒ Prop;
	simp set_eq__def.

lemma set_eq__intro:
	if iff: ∀x. x : 'a ⟹ p x ⟷ q x, ['a : TYPE, p : 'a ⇒ Prop, q : 'a ⇒ Prop]
	then set_eq_ 'a p q;
	simp set_eq__def; apply all_intro;
	- if [x : 'a] then p x ⟷ q x; apply iff.
	.

lemma set_eq__elim1: for 'a
	if eq: set_eq_ 'a p q, ['a : TYPE, p : 'a ⇒ Prop, q : 'a ⇒ Prop, x : 'a]
	then p x ⟷ q x;
	apply eq[simp set_eq__def, THEN all_elim1[of x]].

instance Set: QuotientType TYPE ('a. 'a ⇒ Prop) set_eq_ ;
	- by is_set__type.
	- if ['a : TYPE]; by #simp set_eq__def.
	- if ['a : TYPE]; apply equivalence_intro;
		- apply symmetric_intro;
			- if eq: set_eq_ 'a p q, ...;
				apply set_eq__intro;
				- if [x : 'a]; apply iff.sym; by set_eq__elim1[OF eq].
				.
			.
		- apply reflexive_intro; by set_eq__intro #elim set_eq__elim1.
		- apply transitive_intro;
			- if pq: set_eq_ 'a p q, qr: set_eq_ 'a q r, ... then set_eq_ 'a p r;
				apply set_eq__intro;
				- if [x : 'a] then p x ⟷ r x;
					.. ⟷ q x; apply set_eq__elim1[OF pq].
					apply set_eq__elim1[OF qr].
				.
			.
		.
	.

definition Set = Set.Abs.

definition[as _has] (∋) = Set.rep.

definition[as _in] (∈) =
	(IMPLICIT 'a : TYPE. 'a) (fun 'a : TYPE, x : 'a, A : Set 'a. Set.rep A x).

lemma in_def: if ['a : TYPE, x : 'a, A : Set 'a] then (x ∈ A) = Set.rep A x;
	simp _in_def IMPLICIT[of 'a].

lemma in_type#intro[after 1] for 'a if [A : Set 'a, 'a : TYPE, x : 'a] then x ∈ A : Prop;
	by #simp in_def[of 'a] Set_def[dual] #intro Set.rep_type[of 'a, THEN to_elim1].

definition[as Collect] {_:_} = (Set.abs ∘) ∘ (fun_:).

lemma Collect_type!
	if ['a : TYPE, ∀x. x : 'a ⟹ P.[x] : Prop] then {x : 'a. P.[x]} : Set 'a;
	simp Collect_def Set_def; apply Set.abs_type.

lemma in_Collect_type!
	if ['a : TYPE, ∀x. x : 'a ⟹ P.[x] : Prop, s : 'a] then s ∈ {x : 'a. P.[x]} : Prop;
	apply in_type[of 'a].

lemma in_Collect#simp
	if ['a : TYPE, x : 'a, ∀y. y : 'a ⟹ F.[y] : Prop]
	then (x ∈ {x : 'a. F.[x]}) ⟷ F.[x];
	.. = Set.rep (Set.abs (fun x' : 'a. F.[x'])) x;
		simp Collect_def in_def[of 'a].
	.. ⟷ (fun x' : 'a. F.[x']) x;
		apply set_eq__elim1[of 'a], Set.rep_abs_sim[of 'a];
		by Set.rep_type Set.abs_type.
	by Set.rep_type[of 'a, THEN to_elim1] Set.abs_type[of 'a].

lemma set_eq_intro:
	if eq: ∀x. x : 'a ⟹ x ∈ X ⟷ x ∈ X', ['a : TYPE, X : Set 'a, X' : Set 'a]
	then X = X';
	apply Set.eq_intro[of 'a], set_eq__intro;
	- if [x : 'a]; fold in_def[of 'a]; by eq.
	by Set.rep_type #simp Set_def[dual].


definition empty_ = (fun 'a : TYPE. {x : 'a. false}).

lemma in_empty_ : if ['a : TYPE, x : 'a] then x ∈ empty_ 'a ⟷ false;
	simp empty__def; apply in_Collect.

definition[as singleton] {_} = (IMPLICIT 'a : TYPE. 'a) (fun 'a : TYPE, x : 'a. {y : 'a. x = y}).

lemma in_singleton:
	if ['a : TYPE, x : 'a, y : 'a]
	then x ∈ {y} ⟷ y = x;
	simp singleton_def IMPLICIT[of 'a]; simp[on (⟷)].

definition[as cup] (∪) = (IMPLICIT 'a : TYPE. Set 'a)
	(fun 'a : TYPE, A B : Set 'a. {x : 'a. x ∈ A ∨ x ∈ B}).

lemma in_cup_iff: if ['a : TYPE, x : 'a, X : Set 'a, Y : Set 'a]
	then x ∈ X ∪ Y ⟷ x ∈ X ∨ x ∈ Y;
	simp cup_def IMPLICIT[of 'a]; simp[on (⟷)].

definition[as cap] (∩) = (IMPLICIT 'a : TYPE. Set 'a)
	(fun 'a : TYPE, A B : Set 'a. {x : 'a. x ∈ A ∧ x ∈ B}).

lemma in_cap_iff: if ['a : TYPE, x : 'a, X : Set 'a, Y : Set 'a]
	then x ∈ X ∩ Y ⟷ x ∈ X ∧ x ∈ Y;
	simp cap_def IMPLICIT[of 'a]; simp[on (⟷)].
