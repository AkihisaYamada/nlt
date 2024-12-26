------
# Typed Intuitionistic Logic
------

base Root;

fix prop (∧) (∨) (⟺) (¬) (∃);

import Prop;
import PropTrue;
import PropFalse;
import MinimalNot;
import not: Unary prop (¬);
import PropAnd;
import PropIff;
import PropOr;
import ex: Binder prop (∃);
import PropOr;
import PropEx;

finalize;

interpret TypeFreeMinimal;

setup rewrite iff_elim1 iff.refl iff.trans;
setup dual iff.sym;

setup cong iff_cong_imp iff_cong_iff iff_cong_and iff_cong_not iff_cong_all;

setup conclude iff.refl true_intro;


show not_imp_iff_false: if nP: ¬P, pP: prop P then P ⟺ false :=
	apply iff_intro;
	case P: P :=
		by not_imp_false[OF nP P];
	case f: false :=
		by false_elim[OF f pP];
	qed;

show false_imp_iff: if pP: prop P then (false ⟹ P) ⟺ true :=
	apply iff_true;
	case f: false :=
		by false_elim[OF f pP];
	qed;

show false_and_iff: if pP: prop P then false ∧ P ⟺ false :=
	apply iff_intro;
	show! if fP: false ∧ P then false :=
		by and_elim1[OF fP];
	show! if f: false then false ∧ P :=
		apply and_intro;
		by f false_elim[OF f pP];
	qed;

show and_false_iff: if pP: prop P then P ∧ false ⟺ false :=
	unfold and_iff.commute;
	by false_and_iff[OF pP];

show not_elim: if nP: ¬P, P: P, pQ: prop Q then Q :=
	show f: false :=
		by not_imp_false[OF nP P];
	by false_elim[OF f pQ];




