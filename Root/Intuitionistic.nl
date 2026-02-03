-------
# Intuitionistic Logic
-------

import Minimal.

assume false_elim: if false then P.

begin

lemma not_imp_iff_false: if nP: ¬P then P ⟺ false;
	apply iff_intro;
	-; by not_imp_false[OF nP].
	by #elim false_elim.

lemma false_imp_iff(simp) (false ⟹ P) ⟺ true;
	by iff_true #elim false_elim.

namespace iff:
	interpret iff.
	interpret and: iff.MetaCommMonoidAbsorb (∧) false true;
		- for P then false ∧ P ⟺ false;
			by iff_intro #elim false_elim.
		.
	interpret or: iff.MetaCommMonoidAbsorb (∨) true false;
		- for P then false ∨ P ⟺ P;
			by iff_intro or_intro #elim or_elim false_elim.
		.
end

note(simp)
	iff.and.left_absorb iff.and.right_absorb
	iff.or.left_neutral iff.or.right_neutral.

lemma not_elim: if nP: ¬P, P: P then Q;
	by false_elim[OF not_imp_false[OF nP P]].

theory Propositional:
	import Propositional.
end

theory FirstOrder:
	import FirstOrder.
begin
	theory Impredicative:
		import Impredicative.
	end
end

theory SecondOrder:
	import SecondOrder.
begin
	theory Impredicative:
		import Impredicative.
	end
end

theory HigherOrder:
	import HigherOrder.
begin
	theory Impredicative:
		import Impredicative.
	end
end
	