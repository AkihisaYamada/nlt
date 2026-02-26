import Eq.
import TypeFree.
import Minimal.
import Ex1.
import Pair.
assume unique_choice: if ∀x. ∃!y. P.[x,y] then ∃f. ∀x. P.[x, f x].

begin

theorem inconsistent: false;
	obtain R where R_def: R x = (x x ⟹ false);
		- for thesis if assm;
			apply unique_choice[of ((x,y). y = (x x ⟹ false)), THEN ex_elim, simp, OF ex1_eq1];
			apply assm>0=.
		.
	have nRR: if RR: R R then false;
		apply RR[unfold R_def, OF RR].
	have RR: R R;
		by nRR[fold R_def].
	by nRR[OF RR].
