-------
# Intuitionistic Logic
-------

import Minimal.

assume false_elim: if false then ∀P. P.

begin

lemma not_imp_iff_false: if nP: ¬P then P ⟺ false;
	apply iff_intro;
	-; by not_imp_false[OF nP].
	by #elim false_elim.

lemma false_imp_iff(simp) (false ⟹ P) ⟺ true;
	by iff_true #elim false_elim.

lemma false_and_iff(simp) false ∧ P ⟺ false;
	by iff_intro #elim and_elim false_elim.

lemma and_false_iff(simp) P ∧ false ⟺ false;
	unfold iff.and.commute;
	by false_and_iff.

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
	