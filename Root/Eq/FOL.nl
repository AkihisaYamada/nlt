import ..FOL.
begin

interpret .Prop.
eaf
theory Minimal:
	import .Prop.Minimal.
eaf
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

theory Ex1:
	fix (∃!∈).
	assume ex1_type: if A ∈ TYPE, ∀x. x ∈ A ⟹ P.[x] ∈ PROP then (∃!x ∈ A. P.[x]) ∈ PROP.
	assume ex1_imp_ex: if ∃!x ∈ A. P.[x], A ∈ TYPE then ∃x ∈ A. P.[x].
	assume ex1_imp_unique:
	if ∃!x ∈ A. P.[x], P.[y], P.[z], A ∈ TYPE, y ∈ A, z ∈ A then y = z.
	assume ex1_intro: for x
	if P.[x], ∀y ∈ A. P.[y] ⟹ y = x, A ∈ TYPE, x ∈ A then ∃!x ∈ A. P.[x].
end

theory UniqueChoiceOp:
	fix (∃!∈) THE_IN.
	import Ex1.
	assume THE_type: if ∃!x ∈ A. P.[x], A ∈ TYPE then (THE x ∈ A. P.[x]) ∈ A.
	assume THE: if ∃!x ∈ A. P.[x], A ∈ TYPE then P.[THE x ∈ A. P.[x]].
end

