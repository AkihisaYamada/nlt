import Membership.
fix TYPE.

begin

theory FunInType:
	fix (FunIn).
	assume FunIn_TYPE: if A ∈ U, ∀x ∈ A. B.[x] ∈ U then (FUN x ∈ A. B.[x]) ∈ TYPE U.
end




