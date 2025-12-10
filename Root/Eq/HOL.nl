import ..HOL.
begin

interpret FOL.

theory Minimal:
	import ..Minimal.
end

theory Intuitionistic:
	import ..Intuitionistic.
begin
	interpret Minimal.
end

theory Classical:
	import ..Classical.
begin
	interpret Intuitionistic.
end


