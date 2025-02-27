------
# Typed Intuitionistic Logic
------

base Root;

import Propositional;

---
We specify false.
---
obtain false where false_elim: ∀P. false ⟹ prop P ⟹ P, [prop false] :=
	- for thesis, if assm: ∀false. (∀P. false ⟹ prop P ⟹ P) ⟹ prop false ⟹ thesis :=
		apply assm(∀P. prop P ⟹ P);
		- for P, if f: ∀P. prop P ⟹ P, [prop P] :=
			apply f;
			done;
		done;
	qed;

interpret false: Member prop false :=
	- prop false :=
		done;
	end;

import TypedMinimalLogic;

finalize;

setup rewrite iff_imp iff_imp_rev iff.refl iff.trans;
setup dual iff.sym;
setup cong iff_cong_imp iff_cong_iff iff_cong_all iff_cong_not iff_cong_and iff_cong_or;

show not_imp_iff_false: if nP: ¬P, [prop P] then P ⟺ false :=
	apply iff_intro;
	- := by not_imp_false[OF nP];
	- if f: false :=
		apply false_elim[OF f];
		done;
	done;

show false_imp_iff: if [prop P] then (false ⟹ P) ⟺ true :=
	apply iff_true;
	- if f: false :=
		apply false_elim[OF f];
		done;
	done;

show false_and_iff: if [prop P] then false ∧ P ⟺ false :=
	apply iff_intro;
	- if and: false ∧ P :=
		by and_elim1[OF and];
	- if f: false :=
		apply false_elim[OF f];
		done;
	done;

show and_false_iff: if [prop P] then P ∧ false ⟺ false :=
	unfold and_iff.commute;
	by false_and_iff;

show not_elim: if nP: ¬P, P: P, [prop P, prop Q] then Q :=
	apply false_elim;
	by not_imp_false[OF nP P];
