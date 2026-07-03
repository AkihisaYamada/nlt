import Eq, Membership.

fix (fun).

assume fun_app: for A if s ∈ A then (fun x. F.[x]) s = F.[s].

begin

theory FunType :=
	import Std.FunType.
	assume fun_in_type: if ∀x ∈ A. F.[x] ∈ B then (fun x. F.[x]) ∈ A → B.
end

theory DepFunType :=
	import Std.DepFunType.
	assume fun_in_FunIn! if ∀x ∈ A. F.[x] ∈ B.[x] then (fun x. F.[x]) ∈ (FUN x ∈ A. B.[x]).
begin

end
