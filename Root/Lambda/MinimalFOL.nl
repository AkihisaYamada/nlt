base Lambda.

import Prop.
import TypedAll.

begin

interpret TypedTrue;
	obtain true where ! prop true, ! true;
		- for thesis, if assm;
			apply assm[of (∀P:prop. P ⟹ P)];
			by all_intro.
		.
	.

define[and] P ∧ Q := ∀R:prop. (P ⟹ Q ⟹ R) ⟹ R.
define[or] P ∨ Q := ∀R:prop. (P ⟹ R) ⟹ (Q ⟹ R) ⟹ R.
define[ex] (∃:) ι P := ∀Q:prop. (∀x:ι. P.[x] ⟹ Q) ⟹ Q.

interpret TypedAnd;
	by all_intro #unfold and_def #elim all_elim.

interpret TypedOr;
	- by #unfold or_def.
	- for P Q, if !P, !prop P, !prop Q then P ∨ Q;
		unfold or_def;
		apply all_intro;
		- for R, if !prop R, !P ⟹ R, : Q ⟹ R then R.
		.
	- for P Q, if !Q, !prop P, !prop Q then P ∨ Q;
		unfold or_def;
		apply all_intro;
		- for R, if !prop R, :P ⟹ R, !Q ⟹ R then R.
		.
	- for P Q, if PQ: P ∨ Q;
		- for R, if PR, QR, !, !, !;
			apply PQ[unfolded or_def, THEN all_elim1];
			-.
			-.
			- by PR.
			- by QR.
			.
		.
	.

interpret MinimalPL.

setup rewrite iff_imp iff_imp_rev iff.refl iff.trans.
setup dual iff.sym.

interpret TypedEx;
	-.
	- by #unfold ex_def.
	- for x P ι, if !P.[x], !ι x, ! ∀y. ι y ⟹ prop P.[y] then ∃y:ι. P.[y];
		unfold ex_def;
		apply all_intro;
		- for Q, if !prop Q, all: ∀y:ι. P.[y] ⟹ Q then Q;
			apply all_elim1[OF all, of x].
		.
	- for ι P, if ex: ∃x:ι. P.[x];
		- for Q, if all: ∀x. P.[x] ⟹ ι x ⟹ Q, ! ∀x. ι x ⟹ prop P.[x], ! prop Q;
			apply ex[unfolded ex_def, THEN all_elim1];
			-.
			-.
			apply all_intro;
			- for x;
				by all[of x].
			.
		.
	.

interpret ..MinimalFOL.

