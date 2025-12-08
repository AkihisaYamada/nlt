---
# Intuitionistic Propositional Logic
---

import Minimal.
assume false_elim: false ⟹ ∀P. P ∈ PROP ⟹ P.

begin

lemma not_imp_iff_false: if nP: ¬P, [P ∈ PROP] then P ⟺ false;
	by iff_intro not_imp_false[OF nP] #elim false_elim.

lemma imp_false_imp_iff_false: if P0: P ⟹ false, [P ∈ PROP] then P ⟺ false;
	by not_imp_iff_false not_intro P0.

lemma false_imp_iff: if [P ∈ PROP] then (false ⟹ P) ⟺ true;
	by iff_true #elim false_elim.

namespace iff begin
	interpret ..iff.

	namespace and begin
		interpret ..and.

		interpret CommMonoidAbsorb (∧) false true;
			for P if !P ∈ PROP then false ∧ P ⟺ false;
				apply iff_intro;
				if and: false ∧ P;
					by and_elim1[OF and].
				by #elim false_elim.
			.
	end

end

lemma not_elim: if nP: ¬P, P: P, [P ∈ PROP, Q ∈ PROP] then Q;
	have f: false;
		by not_imp_false[OF nP P].
	apply false_elim[OF f].

theory Irreflexive:
	import ..Irreflexive.
begin
	lemma refl_iff: if ! x ∈ A then x < x ⟺ false;
		by not_imp_iff_false irrefl.
end