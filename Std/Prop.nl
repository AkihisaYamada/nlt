---
# Propositions

We fix a class `Prop` in which logical operators are closed.
---
fix Prop.
import? Membership (:), To.

begin

instance imp: Magmas (⟹) (:).

extend Std.Membership begin

	theory Relation A (⊏) :=
		assume prop! if x ∈ A, y ∈ A then x ⊏ y : Prop.
	end

end

instance Membership (:).

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

---
*Quantifiable* theories allow quantification over certain types.
We denote the class of types one can quantify over by `QTYPE` (for "quantifiable type").
---
theory Quantifiable QTYPE (∀:) (∃:) :=
	import AllRelStrict QTYPE (:) (∀:).
	import ExRelStrict QTYPE (:) (∃:).
begin

	---
	A theory is called *impredicative* if quantification over propositions are allowed.
	This property can be simply characterized by saying `Prop` is a `QTYPE`.
	---
	theory Impredicative :=
		assume prop_quantifiable! Prop : QTYPE.
	begin

		definition false := ∀P : Prop. P.

		instance Prop.False;
			- apply false_def_intro[of (x. x : Prop)].
			- if false;
				note all: false_def_elim[of (x. x), OF false].
				apply all_elim1[OF all ! !]=.
			.

	end

end

theory FirstOrder IND :=
	import Quantifiable IND.
end

---
A *second-order* theory allows quantification over functions over individuals.
This restriction requires to split individuality from quantifiability.
Note that whether to consider predicates quantifiable or not is impredicativity, orthogonal to the order.
---
theory SecondOrder IND :=
	import Quantifiable.
	assume ind_quantifiable: if A : IND then A : QTYPE.
	assume to_quantifiable! if A : IND, B : QTYPE then A → B : QTYPE.
begin

	instance FirstOrder IND;
		note! ind_quantifiable.
		- for x if Px: P.[x], [x : A], ... then ∃x' : A. P.[x'];
			apply ex_intro1[of x, OF Px].
		- if ex: ∃x : A. P.[x] for Q if assm, ... then Q;
			apply ex_elim[OF ex];
			- for x; by assm[of x].
			.
		.

end

---
*Predicative higher-order* theories allow quantification over functions over quantifiable types.  
---
theory HigherOrder :=
	import Quantifiable.
	assume to_quantifiable! if A : QTYPE, B : QTYPE then A → B : QTYPE.
begin

	instance? SecondOrder QTYPE.

end

theory FreeOrder :=
	import AllRel (:) (∀:).
	import ExRel (:) (∃:).
begin

end


---
The presence of the choice operator requires that every type `A` is inhabited.
We can accommodate empty types by restricting `A` to belong to a certain class `CTYPE`.
---
theory AnySuchTyped CTYPE :=
	fix such_:.
	assume such_type! if A : CTYPE, ∀x. x : A ⟹ P.[x] : Prop then (such x : A. P.[x]) : A.
	assume such_intro1: for x if P.[x], A : CTYPE, x : A, ∀x. x : A ⟹ P.[x] : Prop then P.[such z : A. P.[z]].
begin


end
