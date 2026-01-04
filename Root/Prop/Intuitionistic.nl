---
# Intuitionistic Propositional Logic
---

import Minimal.

namespace false:
	assume elim: false ⟹ ∀P. P ∈ Prop ⟹ P.
end

begin

lemma not_imp_iff_false: if nP: ¬P, [P ∈ Prop] then P ⟺ false;
	by iff.intro not_imp_false[OF nP] #elim false.elim.

lemma imp_false_imp_iff_false: if P0: P ⟹ false, [P ∈ Prop] then P ⟺ false;
	by not_imp_iff_false not.intro P0.

lemma false_imp_iff: if [P ∈ Prop] then (false ⟹ P) ⟺ true;
	by iff_true #elim false.elim.

lemma foo: if [P ∈ Prop] then (false ⟹ P);
	unfold false_imp_iff.

namespace iff:
	interpret iff.

	namespace and:
		interpret and.
		interpret CommMonoidAbsorb (∧) false true;
		- for P if !P ∈ Prop then false ∧ P ⟺ false;
			apply iff.intro;
			- if and: false ∧ P;
				by and.elim1[OF and].
			by #elim false.elim.
		.
	end

end

lemma not_elim: if nP: ¬P, P: P, [P ∈ Prop, Q ∈ Prop] then Q;
	have f: false;
		by not_imp_false[OF nP P].
	apply false.elim[OF f].

theory Irreflexive:
	import Irreflexive.
begin
	lemma refl_iff: if ! x ∈ A then x < x ⟺ false;
		by not_imp_iff_false irrefl.
end