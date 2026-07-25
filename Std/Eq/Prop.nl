---
# Equational Logic

With type-free equality, equations are not necessarily propositions.
---
import ..Prop.
fix Eq.
assume eq_prop! if x ∈ Eq, y ∈ Eq then (x = y) ∈ Prop.

begin

theory Pair :=
	import MetaPair.
	assume pair_eq#intro if x ∈ Eq, y ∈ Eq then (x,y) ∈ Eq.
end

theory FalseNot :=
	fix false.
	assume false_prop! false ∈ Prop.
	import ..FalseNot.
begin
	interpret not: Unary (¬) Prop Prop;
		by #simp not_eq_imp_false.
end

theory Minimal :=
	import FalseNot.
	import Eq.Minimal.
	import and: Magma Prop (∧).
	import or: Magma Prop (∨).
begin

	interpret iff: Magma Prop (⟺).

end

theory Intuitionistic :=
	import FalseNot, Eq.Intuitionistic.
begin
	interpret Minimal.
end

theory Classical :=
	import FalseNot, Eq.Classical.
begin
	interpret Intuitionistic.
end
