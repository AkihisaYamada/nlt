---
# Equality and Propositions

When one declares what are propositions, one need not say equality between any two terms are propositions. Therefore we fix a class `EQTYPE` of types and say equality between two terms of the same `EQTYPE` is a proposition.
---
fix EQTYPE.
import Std_Typed? Std.Typed.
assume eq_prop: if A : EQTYPE, x : A, y : A then (x = y) : Prop.
---
We allow equality between propositions, since otherwise predicates cannot be defined.
---
assume prop_eqtype! Prop : EQTYPE.

begin

instance Eq_Membership? Eq.Membership (:).

theory Ex1Type :=
	fix (∃!:).
	assume EX1_prop! if A : EQTYPE, ∀x. x : A ⟹ P.[x] : Prop then (∃!x : A. P.[x]) : Prop.
	assume EX1_intro1: for x A P
		if P.[x], ∀y. P.[y] ⟹ y : A ⟹ y = x, A : EQTYPE, x : A, ∀x. x : A ⟹ P.[x] : Prop
		then ∃!x : A. P.[x].
	assume EX1_elim:
		if ∃!x : A. P.[x], ∀x. P.[x] ⟹ (∀y. P.[y] ⟹ y : A ⟹ y = x) ⟹ x : A ⟹ Q
		   A : EQ, ∀x. x : A ⟹ P.[x] : Prop
		then Q.
end

theory TypedThe :=
	fix the_:.
	assume the_type! if A : EQTYPE, ∀x. x : A ⟹ P.[x] : Prop then (the x : A. P.[x]) : A.
	assume the_intro1: for x
		if P.[x], ∀y. P.[y] ⟹ y : A ⟹ x = y, A : EQTYPE, x : A, ∀z. z : A ⟹ P.[z] : Prop
		then P.[the z : A. P.[z]].
begin

	lemma the_eq:
		if Px: P.[x], uniq: ∀y. P.[y] ⟹ y : A ⟹ x = y, [A : EQTYPE, x : A, ∀z. z : A ⟹ P.[z] : Prop]
		then (the z : A. P.[z]) = x;
		apply eq.sym;
		apply uniq;
		apply the_intro1[OF Px uniq].

end
