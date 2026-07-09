import Eq.
import Membership.
fix (fun).
assume fun_app#simp[after 1] for A if s ∈ A then (fun x. F.[x]) s = F.[s].

begin

theory FunType :=
	import base.FunType.
	assume fun_in_type: if ∀x ∈ A. F.[x] ∈ B then (fun x. F.[x]) ∈ A → B.
end

theory DepFunType :=
	import base.DepFunType.
	assume fun_in_FunIn! if ∀x ∈ A. F.[x] ∈ B.[x] then (fun x. F.[x]) ∈ (FUN x ∈ A. B.[x]).
begin

end
