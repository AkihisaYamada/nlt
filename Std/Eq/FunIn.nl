fix (fun_:) (:).
assume funIn_app#simp if s : A then (fun x : A. F.[x]) s = F.[s].

begin

instance base? Std.FunIn;
	- for P A F s if P, sA; use sA P.-- the order of assumptions matters.
	.

instance Membership (:).

extend To :=
	import base.To.
end