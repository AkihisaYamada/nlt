---
# Propositions

We fix a class `Prop` in which logical operators are closed.
---
import Membership (:).

fix Prop.
import imp: Magma Prop (⟹).

begin

note! imp.closed.

theory Relation A (⊏) :=
	import Binary (⊏) A A Prop.
begin

	note! closed.

end

theory PierceLaw :=
	assume pierce_law: if (P ⟹ Q) ⟹ P, P : Prop, Q : Prop then P.
end

theory True :=
	fix true.
	assume true_prop! true : Prop.
	assume true_intro! true.
end

theory False :=
	fix false.
	assume false_prop! false : Prop.
	assume false_elim: if false, P : Prop then P.
begin

	instance True;
		obtain true where true_def: if P.[false ⟹ false] then P.[true];
			- for thesis if assm;
				apply assm[of (false ⟹ false)].
			.
		- apply true_def[of (x. x : Prop)].
		- apply true_def[of (x. x)].
		.

end

theory AllRelStrict A (⊏) (∀⊏) :=
	assume all_prop! if a : A, ∀x. x ⊏ a ⟹ P.[x] : Prop then (∀x ⊏ a. P.[x]) : Prop.
	assume all_intro! if ∀x. x ⊏ a ⟹ P.[x], a : A, ∀x. x ⊏ a ⟹ P.[x] : Prop then ∀x ⊏ a. P.[x].
	assume all_elim1: for s if ∀x ⊏ a. P.[x], a : A, ∀x. x ⊏ a ⟹ P.[x] : Prop, s ⊏ a then P.[s].
begin

	lemma all_elim#elim
		if all: ∀x ⊏ a. P.[x], assm: (∀x. x ⊏ a ⟹ P.[x]) ⟹ Q,
		   [a : A, ∀x. x ⊏ a ⟹ P.[x] : Prop]
		then Q;
		apply assm;
		- for x; by all_elim1[of x, OF all].
		.

	lemma arbitrary: if s: s ⊏ a, all: ∀x ⊏ a. P.[x], [a : A, ∀x. x ⊏ a ⟹ P.[x] : Prop] then P.[s];
		by all_elim1[OF all _ _ s].

end

theory ExRelStrict A (⊏) (∃⊏) :=
	assume ex_prop! if a : A, ∀x. x ⊏ a ⟹ P.[x] : Prop then (∃x ⊏ a. P.[x]) : Prop.
	assume ex_intro1: for x if P.[x], x ⊏ a, a : A, ∀x. x ⊏ a ⟹ P.[x] : Prop then ∃x ⊏ a. P.[x].
	assume ex_elim: if ∃x ⊏ a. P.[x], ∀x. P.[x] ⟹ x ⊏ a ⟹ Q, a : A, ∀x. x ⊏ a ⟹ P.[x] : Prop, Q : Prop then Q.
end

theory FirstOrder TYPE (∀:) (∃:) :=
	import AllRelStrict TYPE (:) (∀:).
	import ExRelStrict TYPE (:) (∃:).
begin

	---
	A logic is called *impredicative* if quantification over propositions are allowed.
	This property can be simply characterized by saying `Prop` is a type.
	---
	theory Impredicative :=
		assume prop_type! Prop : TYPE.
	begin

		definition false := ∀P : Prop. P.

		instance False;
			- apply false_def_intro[of (x. x : Prop)].
			- if false;
				note all: false_def_elim[of (x. x), OF false].
				apply all_elim1[OF all ! !]=.
			.

	end

end

theory SecondOrder IND :=
	import FirstOrder, To.
	assume ind_type: if A : IND then A : TYPE.
	assume to_type! if A : IND, B : TYPE then A → B : TYPE.
end

theory HigherOrder :=
	import FirstOrder, To.
	assume to_type! if A : TYPE, B : TYPE then A → B : TYPE.
begin

	instance? SecondOrder TYPE.

end

---
The presence of the choice operator requires that every type `A` is inhabited.
We can accommodate empty types by restricting `A` to belong to a certain class `TYPE`.
---
theory TypedSome TYPE :=
	fix some_:.
	assume some_type! if A : TYPE, ∀x. x : A ⟹ P.[x] : Prop then (some x : A. P.[x]) : A.
	assume some_intro1: for x if P.[x], A : TYPE, x : A, ∀x. x : A ⟹ P.[x] : Prop then P.[some z : A. P.[z]].
begin


end
