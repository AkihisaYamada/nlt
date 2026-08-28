---
# Sets in Intuitionistic HOL

Since we leave extensionality assumptions optional, Gordon's type definition is not sufficient to derive set types. On the other hand, quotient types are sufficient and more direct for deriving set types from intentional intuitionistic logic.
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
	-.
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

lemma Set_type! Set : TYPE ⇒ TYPE; unfold Set_def; apply Set.Abs_type.
note Set_type1! Set_type[THEN to_elim1].

definition[as in] (∈) = dual Set.rep.

lemma Set_rep_as_in: Set.rep A x = (x ∈ A); simp in_def.

lemma in_type#intro[after 1] for 'a if [A : Set 'a, 'a : TYPE, x : 'a] then x ∈ A : Prop;
	by #simp in_def Set_def[dual] #intro Set.rep_type[of 'a, THEN to_elim1].

lemma Set_eq_intro:
	if iff: ∀x. x : 'a ⟹ x ∈ X ⟷ x ∈ X', ['a : TYPE, X : Set 'a, X' : Set 'a]
	then X = X';
	apply Set.eq_intro[of 'a], set_eq__intro;
	- if [x : 'a]; by iff #simp Set_rep_as_in.
	by Set.rep_type #simp Set_def[dual].

definition[as collect] {_:_} = (Set.abs ∘) ∘ (fun_:).

lemma collect_type!
	if ['a : TYPE, ∀x. x : 'a ⟹ P.[x] : Prop] then {x : 'a. P.[x]} : Set 'a;
	simp collect_def Set_def; apply Set.abs_type.

lemma in_collect_type!
	if ['a : TYPE, ∀x. x : 'a ⟹ P.[x] : Prop, s : 'a] then s ∈ {x : 'a. P.[x]} : Prop;
	apply in_type[of 'a].

lemma in_collect#simp
	if ['a : TYPE, x : 'a, ∀y. y : 'a ⟹ F.[y] : Prop]
	then (x ∈ {x : 'a. F.[x]}) ⟷ F.[x];
	.. = Set.rep (Set.abs (fun x' : 'a. F.[x'])) x;
		simp collect_def in_def.
	.. ⟷ (fun x' : 'a. F.[x']) x;
		apply set_eq__elim1[of 'a], Set.rep_abs_sim[of 'a];
		by Set.rep_type Set.abs_type.
	by Set.rep_type[of 'a, THEN to_elim1] Set.abs_type[of 'a].

lemma collect_cong#cong
	if iff: ∀x. intro (x : 'a) ⟹ P.[x] ⟷ P'.[x],
	   ['a : TYPE, ∀x. x : 'a ⟹ P.[x] : Prop, ∀x. x : 'a ⟹ P'.[x] : Prop]
	then {x : 'a. P.[x]} = {x : 'a. P'.[x]};
	apply Set_eq_intro[of 'a];
	- if [x : 'a]; simp[on (⟷)] iff.
	.

definition[as collectIn] {_∈_} =
	(IMPLICIT 'a : TYPE. Set 'a)
	(fun 'a : TYPE, X : Set 'a. {_:_} 'a ∘ _BindAppBind (x. x ∈ X ∧) ).

lemma collectIn_ : for 'a if [X : Set 'a, 'a : TYPE]
	then {x ∈ X. P.[x]} = {x : 'a. x ∈ X ∧ P.[x]};
	unfold[at 0 1, repeat 6] collectIn_def IMPLICIT[of 'a] funIn_app o_app _BindAppBind.

definition empty_ = (fun 'a : TYPE. {x : 'a. false}).

lemma in_empty_ : if ['a : TYPE, x : 'a] then x ∈ empty_ 'a ⟷ false;
	simp empty__def; apply in_collect.

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

lemma cup_collect#simp if ['a : TYPE, ∀x. x : 'a ⟹ P.[x] : Prop, X : Set 'a]
	then X ∪ {x : 'a. P.[x]} = {x : 'a. x ∈ X ∨ P.[x]};
	simp cup_def IMPLICIT[of 'a].

lemma collect_cup#simp if ['a : TYPE, ∀x. x : 'a ⟹ P.[x] : Prop, X : Set 'a]
	then {x : 'a. P.[x]} ∪ X = {x : 'a. P.[x] ∨ x ∈ X};
	simp cup_def IMPLICIT[of 'a].

definition[as cap] (∩) = (IMPLICIT 'a : TYPE. Set 'a)
	(fun 'a : TYPE, A B : Set 'a. {x : 'a. x ∈ A ∧ x ∈ B}).

lemma in_cap_iff: if ['a : TYPE, x : 'a, X : Set 'a, Y : Set 'a]
	then x ∈ X ∩ Y ⟷ x ∈ X ∧ x ∈ Y;
	simp cap_def IMPLICIT[of 'a]; simp[on (⟷)].

lemma cap_collect#simp if ['a : TYPE, ∀x. x : 'a ⟹ P.[x] : Prop, X : Set 'a]
	then X ∩ {x : 'a. P.[x]} = {x : 'a. x ∈ X ∧ P.[x]};
	simp cap_def IMPLICIT[of 'a].

lemma collect_cap#simp if ['a : TYPE, ∀x. x : 'a ⟹ P.[x] : Prop, X : Set 'a]
	then {x : 'a. P.[x]} ∩ X = {x : 'a. P.[x] ∧ x ∈ X};
	simp cap_def IMPLICIT[of 'a].


definition[as allIn] (∀∈) = (IMPLICIT 'a : TYPE. Set 'a)
	(dual ((∘) ∘ ((∘) ∘ (∀:))) ( _BinderApp _BindAppBind (y. (⟶) ∘ (y ∈)))).

lemma allIn_type: for 'a if [A : Set 'a, 'a : TYPE, ∀x. x : 'a ⟹ P.[x] : Prop]
	then (∀x ∈ A. P.[x]) : Prop;
	simp allIn_def IMPLICIT[of 'a].

lemma allIn_iff: for 'a if [A : Set 'a, 'a : TYPE, ∀x. x : 'a ⟹ P.[x] : Prop]
	then (∀x ∈ A. P.[x]) ⟷ (∀x : 'a. x ∈ A ⟶ P.[x]);
	simp allIn_def IMPLICIT[of 'a]; apply all_cong.

lemma allIn_collect#simp
	if ['a : TYPE, ∀x. x : 'a ⟹ P.[x] : Prop, ∀x. x : 'a ⟹ Q.[x] : Prop]
	then (∀x ∈ {x : 'a. P.[x]}. Q.[x]) ⟷ (∀x : 'a. P.[x] ⟶ Q.[x]);
	note! allIn_type[of 'a].
	simp[on (⟷), at 0] allIn_iff[of 'a].

definition[as exIn] (∃∈) = (IMPLICIT 'a : TYPE. Set 'a)
	(dual ((∘) ∘ ((∘) ∘ (∃:))) ( _BinderApp _BindAppBind (y. (∧) ∘ (y ∈)))).

lemma exIn_type: for 'a if [A : Set 'a, 'a : TYPE, ∀x. x : 'a ⟹ P.[x] : Prop]
	then (∃x ∈ A. P.[x]) : Prop;
	simp exIn_def IMPLICIT[of 'a].

lemma exIn_iff: for 'a if [A : Set 'a, 'a : TYPE, ∀x. x : 'a ⟹ P.[x] : Prop]
	then (∃x ∈ A. P.[x]) ⟷ (∃x : 'a. x ∈ A ∧ P.[x]);
	simp exIn_def IMPLICIT[of 'a]; apply ex_cong.

lemma exIn_collect#simp
	if ['a : TYPE, ∀x. x : 'a ⟹ P.[x] : Prop, ∀x. x : 'a ⟹ Q.[x] : Prop]
	then (∃x ∈ {x : 'a. P.[x]}. Q.[x]) ⟷ (∃x : 'a. P.[x] ∧ Q.[x]);
	note! exIn_type[of 'a].
	simp[on (⟷), at 0] exIn_iff[of 'a].

definition[as bigcap] (⋂) = (IMPLICIT 'a : TYPE. Set (Set 'a))
	(fun 'a : TYPE, XX : Set (Set 'a). {x : 'a. ∀X ∈ XX. x ∈ X}).

lemma bigcap_def_ : for 'a if [XX : Set (Set 'a), 'a : TYPE]
	then ⋂XX = {x : 'a. ∀X ∈ XX. x ∈ X};
	note! allIn_type[of (Set 'a)].
	simp bigcap_def IMPLICIT[of 'a].

lemma bigcap_type! if [XX : Set (Set 'a), 'a : TYPE] then ⋂XX : Set 'a;
	unfold bigcap_def_ [of 'a]; by allIn_type[of (Set 'a)].

lemma bigcap_collect: if [∀X. X : Set 'a ⟹ P.[X] : Prop, 'a : TYPE] then
	⋂{X : Set 'a. P.[X]} = {x : 'a. ∀X : Set 'a. P.[X] ⟶ x ∈ X};
	note! allIn_type[of (Set 'a)].
	simp bigcap_def_ [of 'a].

definition[as bigcup] (⋃) = (IMPLICIT 'a : TYPE. Set (Set 'a))
	(fun 'a : TYPE, XX : Set (Set 'a). {x : 'a. ∃X ∈ XX. x ∈ X}).

lemma bigcup_def_ : for 'a if [XX : Set (Set 'a), 'a : TYPE]
	then ⋃XX = {x : 'a. ∃X ∈ XX. x ∈ X};
	note! exIn_type[of (Set 'a)].
	simp bigcup_def IMPLICIT[of 'a].

lemma bigcup_type! if [XX : Set (Set 'a), 'a : TYPE] then ⋃XX : Set 'a;
	unfold bigcup_def_ [of 'a]; by exIn_type[of (Set 'a)].

lemma bigcup_collect: if [∀X. X : Set 'a ⟹ P.[X] : Prop, 'a : TYPE] then
	⋃{X : Set 'a. P.[X]} = {x : 'a. ∃X : Set 'a. P.[X] ∧ x ∈ X};
	note! exIn_type[of (Set 'a)].
	simp bigcup_def_ [of 'a].

