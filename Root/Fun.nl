import Membership.

fix (fun).
assume fun_elim: for P F A if s ∈ A, P.[(fun x. F.[x]) s] then P.[F.[s]].

begin

extend FunType:
	assume fun_in_type: if ∀x ∈ A. F.[x] ∈ B then (fun x. F.[x]) ∈ A → B.
end

extend DepFunType:
	assume fun_in_FunIn! if ∀x ∈ A. F.[x] ∈ B.[x] then (fun x. F.[x]) ∈ (FUN x ∈ A. B.[x]).
begin

end
