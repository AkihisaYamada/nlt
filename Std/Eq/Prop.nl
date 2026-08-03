---
# Equational Logic

With type-free equality, equations are not necessarily propositions.
---
import ..Prop.

begin

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
