base Root;

import PropositionalMinimal;

assume false_elim: false ⟹ prop P ⟹ P;

begin

setup rewrite iff_imp iff_imp_rev iff.refl iff.trans;
setup dual iff.sym;

lemma not_imp_iff_false: if nP: ¬P, [prop P] then P ⟺ false :=
	apply iff_intro;
	- by not_imp_false[OF nP];
	- if f: false :=
		apply false_elim[OF f];
		done;
	done;

lemma imp_false_imp_iff_false: if P0: P ⟹ false, [prop P] then P ⟺ false :=
	by not_imp_iff_false not_intro P0;

lemma false_imp_iff: if [prop P] then (false ⟹ P) ⟺ true :=
	apply iff_true;
	- if f: false :=
		apply false_elim[OF f];
		done;
	done;

lemma false_and_iff: if [prop P] then false ∧ P ⟺ false :=
	apply iff_intro;
	- if and: false ∧ P :=
		by and_elim1[OF and];
	- if f: false :=
		apply false_elim[OF f];
		done;
	done;

lemma and_false_iff: if [prop P] then P ∧ false ⟺ false :=
	unfold and_iff.commute;
	by false_and_iff;

lemma not_elim: if nP: ¬P, P: P, [prop P, prop Q] then Q :=
	apply false_elim;
	by not_imp_false[OF nP P];

locale Relation mem (≤) :=
	import Binary (≤) mem mem prop;
end;

locale Preorder :=
	import Relation;
	import Reflexive;
	import Transitive;
end;

locale StrictOrder mem (<) :=
	import Relation mem (<);
	import Irreflexive;
	import Transitive mem (<);
begin
	note! type;
	lemma refl_iff: if xt! mem x then x < x ⟺ false :=
		by not_imp_iff_false irrefl;
	ctxt;
end;
