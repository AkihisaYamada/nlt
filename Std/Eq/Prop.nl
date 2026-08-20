---
# Equality and Propositions

When one declares what are propositions, one need not say equality between any two terms are propositions. Therefore we fix a class `EQTYPE` of types and say equality between two terms of the same `EQTYPE` is a proposition.
---
fix EQTYPE.
import Std_Prop? Std.Prop.
assume eq_prop: if 'a : EQTYPE, x : 'a, y : 'a then (x = y) : Prop.
---
We allow equality between propositions, since otherwise predicates cannot be defined.
---
assume prop_eqtype! Prop : EQTYPE.

begin

---
If one side of an equation is typed, then one should type check the other.
However, it is not the case e.g. subtypes are considered.
---
lemma eq_prop1#intro[after 1] if [x : 'a, 'a : EQTYPE, y : 'a] then x = y : Prop;
	apply eq_prop[of 'a].

lemma eq_prop2#intro[after 1] if [y : 'a, 'a : EQTYPE, x : 'a] then x = y : Prop;
	apply eq_prop[of 'a].

instance Eq_Membership? Eq.Membership (:).

theory Ex1Typed :=
	fix (∃!:).
	assume EX1_prop! if 'a : EQTYPE, ∀x. x : 'a ⟹ P.[x] : Prop then (∃!x : 'a. P.[x]) : Prop.
	assume EX1_intro1: for x 'a P
		if P.[x], ∀y. P.[y] ⟹ y : 'a ⟹ y = x, 'a : EQTYPE, x : 'a, ∀x. x : 'a ⟹ P.[x] : Prop
		then ∃!x : 'a. P.[x].
	assume EX1_elim:
		if ∃!x : 'a. P.[x], ∀x. P.[x] ⟹ (∀y. P.[y] ⟹ y : 'a ⟹ y = x) ⟹ x : 'a ⟹ Q
		   'a : EQ, ∀x. x : 'a ⟹ P.[x] : Prop
		then Q.
end

theory UniqueSuchTyped :=
	fix such_:.
	assume such_type! if 'a : EQTYPE, ∀x. x : 'a ⟹ P.[x] : Prop then (such x : 'a. P.[x]) : 'a.
	assume unique_such_intro1: for x
		if P.[x], ∀y. P.[y] ⟹ y : 'a ⟹ x = y, 'a : EQTYPE, x : 'a, ∀z. z : 'a ⟹ P.[z] : Prop
		then P.[such z : 'a. P.[z]].
begin

	lemma such_eq_intro:
		if Px: P.[x], uniq: ∀y. P.[y] ⟹ y : 'a ⟹ x = y, ['a : EQTYPE, x : 'a, ∀z. z : 'a ⟹ P.[z] : Prop]
		then (such z : 'a. P.[z]) = x;
		apply eq.sym, uniq, unique_such_intro1[OF Px uniq].


end
