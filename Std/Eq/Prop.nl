---
# Equality and Propositions

When one declares what are propositions, one need not say equality between any two terms are propositions. Therefore we fix a class `EQTYPE` of types and say equality between two terms of the same `EQTYPE` is a proposition.
---
fix EQTYPE.
import Std_Prop? Std.Prop.
assume eq_prop: if A : EQTYPE, x : A, y : A then (x = y) : Prop.
---
We allow equality between propositions, since otherwise predicates cannot be defined.
---
assume prop_eqtype! Prop : EQTYPE.

begin

---
If one side of an equation is typed, then one should type check the other.
However, it is not the case e.g. subtypes are considered.
---
lemma eq_prop1#intro[after 1] if [x : A, A : EQTYPE, y : A] then x = y : Prop;
	apply eq_prop[of A].

lemma eq_prop2#intro[after 1] if [y : A, A : EQTYPE, x : A] then x = y : Prop;
	apply eq_prop[of A].

instance Eq_Membership? Eq.Membership (:).

theory Ex1Typed :=
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

theory IfTyped :=
	fix IF.
	assume IF_then: if P, A : EQTYPE, P : Prop, t : A, e : A then IF A P t e = t.
	assume IF_else: if P ⟹ t = e, A : EQTYPE, P : Prop, t : A, e : A then IF A P t e = e.
end

theory UniqueSuchTyped :=
	fix such_:.
	assume such_type! if A : EQTYPE, ∀x. x : A ⟹ P.[x] : Prop then (such x : A. P.[x]) : A.
	assume unique_such_intro1: for x
		if P.[x], ∀y. P.[y] ⟹ y : A ⟹ x = y, A : EQTYPE, x : A, ∀z. z : A ⟹ P.[z] : Prop
		then P.[such z : A. P.[z]].
begin

	lemma such_eq_intro:
		if Px: P.[x], uniq: ∀y. P.[y] ⟹ y : A ⟹ x = y, [A : EQTYPE, x : A, ∀z. z : A ⟹ P.[z] : Prop]
		then (such z : A. P.[z]) = x;
		apply eq.sym, uniq, unique_such_intro1[OF Px uniq].


end
