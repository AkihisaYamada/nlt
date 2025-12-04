---
# Intuitionistic Propositional Logic
---

import MinimalPL.
assume false_elim: false ⟹ ∀P. P : prop ⟹ P.

begin

lemma not_imp_iff_false: if nP: ¬P, [P : prop] then P ⟺ false;
	by iff_intro not_imp_false[OF nP] #elim false_elim.

lemma imp_false_imp_iff_false: if P0: P ⟹ false, [P : prop] then P ⟺ false;
	by not_imp_iff_false not_intro P0.

lemma false_imp_iff: if [P : prop] then (false ⟹ P) ⟺ true;
	by iff_true #elim false_elim.

lemma false_and_iff: if [P : prop] then false ∧ P ⟺ false;
	apply iff_intro;
	if and: false ∧ P;
		by and_elim1[OF and].
	by #elim false_elim.

lemma and_false_iff: if [P : prop] then P ∧ false ⟺ false;
	unfold and_iff.commute;
	by false_and_iff.

lemma not_elim: if nP: ¬P, P: P, [P : prop, Q : prop] then Q;
	have f: false;
		by not_imp_false[OF nP P].
	apply false_elim[OF f].

theory Preorder:
	import Relation.
	import Reflexive.
	import Transitive.
end

theory StrictOrder σ (<):
	import Relation σ (<).
	import Irreflexive σ (<).
	import Transitive σ (<).
begin
	note! type.
	lemma refl_iff: if ! x : σ then x < x ⟺ false;
		by not_imp_iff_false irrefl.
end
