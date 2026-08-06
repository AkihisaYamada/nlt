fix (fun_:) (:).
assume funIn_app#simp if s : A then (fun x : A. F.[x]) s = F.[s].

begin

interpret base? Std.FunIn;
	- for P A F s if P, sA; use sA P.-- the order of assumptions matters.
	.

interpret Membership (:).

extend To :=
	import base.To.
end