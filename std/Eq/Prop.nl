---
# Equational Logic

With type-free equality, equations are not necessarily propositions.
---
import ..Prop.
fix Eq.
assume eq_prop! if x ∈ Eq, y ∈ Eq then (x = y) ∈ Prop.

begin

theory Pair:
	import Pair.
	assume pair_eq(intro) if x ∈ Eq, y ∈ Eq then (x,y) ∈ Eq.
end

theory Minimal:
	import Minimal.
begin

end

theory Intuitionistic:
	import Intuitionistic.
begin
	interpret Minimal.
end

theory Classical:
	import Classical.
begin
	interpret Intuitionistic.
end
