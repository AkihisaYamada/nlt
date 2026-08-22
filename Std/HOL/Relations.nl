begin

theory relation 'a (⊏) :=
	assume TYPE! 'a : TYPE.
	assume relation_type! (⊏) : 'a ⇒ 'a ⇒ Prop.
begin

	note relation_type1! relation_type[THEN to_elim1].
	note relation_type2! relation_type1[THEN to_elim1].

end

definition reflexive = (fun 'a : TYPE, (⊑) : 'a ⇒ 'a ⇒ Prop. ∀x : 'a. x ⊑ x).

lemma reflexive_eq:
	if ['a : TYPE, (⊑) : 'a ⇒ 'a ⇒ Prop] then reflexive 'a (⊑) = (∀x : 'a. x ⊑ x);
	simp reflexive_def.

lemma reflexive_intro:
	if [∀x. x : 'a ⟹ x ⊑ x, 'a : TYPE, (⊑) : 'a ⇒ 'a ⇒ Prop]
	then reflexive 'a (⊑);
	interpret relation 'a (⊑).
	by #simp reflexive_eq.

lemma reflexive_prop!
	if ['a : TYPE, (⊑) : 'a ⇒ 'a ⇒ Prop] then reflexive 'a (⊑) : Prop;
	interpret relation 'a (⊑).
	by #simp reflexive_eq.

theory reflexive 'a (⊑) :=
	import relation 'a (⊑).
	assume reflexive: reflexive 'a (⊑).
begin

	instance Reflexive 'a (⊑); by reflexive[simp reflexive_eq, THEN all_elim1].

end

definition transitive = (fun 'a : TYPE, (⊏) : 'a ⇒ 'a ⇒ Prop. ∀x y z : 'a. x ⊏ y ⟶ y ⊏ z ⟶ x ⊏ z).

lemma transitive_eq:
	if ['a : TYPE, (⊏) : 'a ⇒ 'a ⇒ Prop] then transitive 'a (⊏) = (∀x y z : 'a. x ⊏ y ⟶ y ⊏ z ⟶ x ⊏ z);
	simp transitive_def.

lemma transitive_intro:
	if 1: ∀x y. x ⊑ y ⟹ ∀z. y ⊑ z ⟹ x : 'a ⟹ y : 'a ⟹ z : 'a ⟹ x ⊑ z, ['a : TYPE, (⊑) : 'a ⇒ 'a ⇒ Prop]
	then transitive 'a (⊑);
-	interpret relation 'a (⊑).
	simp transitive_eq;
	apply all_intro;
	- for x if ...; apply all_intro;
		- for y if ...; apply all_intro;
			- for z if ...; by 1[of x y].
			.
		.
	.
.

lemma transitive_prop!
	if ['a : TYPE, (⊑) : 'a ⇒ 'a ⇒ Prop] then transitive 'a (⊑) : Prop;
	interpret relation 'a (⊑).
	by #simp transitive_eq.

theory transitive 'a (⊏) :=
	import relation 'a (⊏).
	assume transitive: transitive 'a (⊏).
begin

	instance Transitive 'a (⊏);
		- if xy: x ⊏ y, yz: y ⊏ z, ... then x ⊏ z;
			note 1: transitive[simp transitive_eq].
			note 2: 1[THEN all_elim1[of x], OF ! ! !].
			note 3: 2[THEN all_elim1[of y], OF ! ! !].
			note 4: 3[THEN all_elim1[of z], OF ! ! !].
			note 5: 4[THEN imp_elim1, OF xy ! !].
			apply 5[THEN imp_elim1, OF yz ! !].
		.

end

definition symmetric = (fun 'a : TYPE, (~) : 'a ⇒ 'a ⇒ Prop. ∀x y : 'a. x ~ y ⟶ y ~ x).
lemma symmetric_eq:
	if ['a : TYPE, (~) : 'a ⇒ 'a ⇒ Prop] then symmetric 'a (~) = (∀x y : 'a. x ~ y ⟶ y ~ x);
	simp symmetric_def.

lemma symmetric_prop!
	if ['a : TYPE, (~) : 'a ⇒ 'a ⇒ Prop] then symmetric 'a (~) : Prop;
	interpret relation 'a (~).
	by #simp symmetric_def.

lemma symmetric_intro:
	if 1: ∀x y. x ~ y ⟹ x : 'a ⟹ y : 'a ⟹ y ~ x, ['a : TYPE, (~) : 'a ⇒ 'a ⇒ Prop]
	then symmetric 'a (~);
-	interpret relation 'a (~).
	unfold symmetric_eq; apply all_intro;
	- if [x : 'a]; apply all_intro;
		- if [y : 'a]; by 1[of x y].
		.
	.
.

theory symmetric 'a (~) :=
	import relation 'a (~).
	assume symmetric: symmetric 'a (~).
begin

	instance Symmetric 'a (~);
		- if xy: x ~ y, ... then y ~ x;
			note 1: symmetric[simp symmetric_eq].
			note 2: 1[THEN all_elim1[of x], OF ! ! !].
			note 3: 2[THEN all_elim1[of y], OF ! ! !].
			by 3[THEN imp_elim1, OF xy].
		.

end

definition preorder = (fun 'a : TYPE, (⊑) : 'a ⇒ 'a ⇒ Prop. reflexive 'a (⊑) ∧ transitive 'a (⊑)).

lemma preorder_eq:
	if ['a : TYPE, (⊑) : 'a ⇒ 'a ⇒ Prop] then preorder 'a (⊑) = (reflexive 'a (⊑) ∧ transitive 'a (⊑));
	simp preorder_def.

lemma preorder_intro:
	if [reflexive 'a (⊑), transitive 'a (⊑), 'a : TYPE, (⊑) : 'a ⇒ 'a ⇒ Prop]
	then preorder 'a (⊑);
	by #simp preorder_eq.

theory preorder 'a (⊑) :=
	import relation 'a (⊑).
	assume preorder: preorder 'a (⊑).
begin

	note preorder_axioms: preorder[simp preorder_eq].

	instance reflexive 'a (⊑);
		show: reflexive 'a (⊑); use preorder_axioms.
		.
	instance transitive 'a (⊑);
		show: transitive 'a (⊑); use preorder_axioms.
		.
	instance Preorder 'a (⊑).

end

definition partial_equivalence =
	(fun 'a : TYPE, (~) : 'a ⇒ 'a ⇒ Prop. symmetric 'a (~) ∧ transitive 'a (~)).

lemma partial_equivalence_eq:
	if ['a : TYPE, (~) : 'a ⇒ 'a ⇒ Prop]
	then partial_equivalence 'a (~) = (symmetric 'a (~) ∧ transitive 'a (~));
	simp partial_equivalence_def.

lemma partial_equivalence_intro:
	if [symmetric 'a (~), transitive 'a (~), 'a : TYPE, (~) : 'a ⇒ 'a ⇒ Prop]
	then partial_equivalence 'a (~);
	by #simp partial_equivalence_eq.

theory partial_equivalence 'a (~) :=
	import relation 'a (~).
	assume partial_equivalence: partial_equivalence 'a (~).
begin

	note partial_equivalence_axioms: partial_equivalence[unfold partial_equivalence_eq].

	instance symmetric 'a (~);
		show: symmetric 'a (~); use partial_equivalence_axioms.
		.
	instance transitive 'a (~);
		show: transitive 'a (~); use partial_equivalence_axioms.
		.
	instance PartialEquivalence 'a (~).

end

definition equivalence =
	(fun 'a : TYPE, (~) : 'a ⇒ 'a ⇒ Prop. symmetric 'a (~) ∧ reflexive 'a (~) ∧ transitive 'a (~)).

lemma equivalence_eq:
	if ['a : TYPE, (~) : 'a ⇒ 'a ⇒ Prop]
	then equivalence 'a (~) = (symmetric 'a (~) ∧ reflexive 'a (~) ∧ transitive 'a (~));
	simp equivalence_def.

lemma equivalence_intro:
	if [symmetric 'a (~), reflexive 'a (~), transitive 'a (~), 'a : TYPE, (~) : 'a ⇒ 'a ⇒ Prop]
	then equivalence 'a (~);
	by #simp equivalence_eq.

theory equivalence 'a (~) :=
	import relation 'a (~).
	assume equivalence: equivalence 'a (~).
begin

	note equivalence_axioms: equivalence[unfold equivalence_eq].

	instance symmetric 'a (~);
		show: symmetric 'a (~); use equivalence_axioms.
		.
	instance reflexive 'a (~);
		show: reflexive 'a (~); use equivalence_axioms.
		.
	instance transitive 'a (~);
		show: transitive 'a (~); use equivalence_axioms.
		.
	instance partial_equivalence 'a (~);
		show: partial_equivalence 'a (~); by symmetric transitive #simp partial_equivalence_eq.
		.
	instance preorder 'a (~);
		show: preorder 'a (~); by reflexive transitive #simp preorder_eq.
		.
	instance Equivalence 'a (~).

end
