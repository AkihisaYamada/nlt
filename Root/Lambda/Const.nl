base Lambda.Logic.

import The.

-----
## More Axioms for Constructors
-----

fix Const is_const.
assume Const_is_const: is_const Const.
assume Const_neq_app: is_const c ⟹ Const ≠ c x.
assume const_app: is_const c ⟹ is_const (c x).
assume const_app_eq_app: is_const c ⟹ is_const d ⟹ c x = d y ⟹ c = d ∧ x = y.

begin

define const_arg v := THE x. ∃c. is_const c ∧ v = c x.

thm const_arg_def.

lemma const_arg: if c: is_const c then const_arg (c x) = x;
	unfold const_arg_def,
	apply ex1_imp_THE_eq,
	apply ex1_intro(x),
	apply ex_intro1(c),
	apply and_intro,
	- by c.
	- .
	- for y, if ex: ∃c'. is_const c' ∧ c x = c' y then x = y;
		obtain c' where c': is_const c', cc': c x = c' y;
			- for P;
				note 1: ex[unfolded ex_def].
				note 2: 1[unfolded(⟺) and_imp_iff].
				apply 2=.
			.
		note and: const_app_eq_app[OF c c' cc'].
		by and_elim2[OF and].
	have! ∃c'. is_const c' ∧ c x = c' x;
		apply ex_intro1(c),
		apply and_intro,
		by c.
	.

