fix true false (∧) (∨).
import Lambda.
import Prop.
import TypedTrue.
import false: Member prop false.
import TypedAnd.
import TypedOr.

begin

setup rewrite eq_imp eq_imp_rev eq.refl eq.trans.
setup dual eq.sym.

setup define beta.

note! false.type.

define[not] ¬P := P ⟹ false.

interpret TypedNot;
	by #unfold not_def.

define[iff] P ⟺ Q := (P ⟹ Q) ∧ (Q ⟹ P).

interpret PropositionalMinimal;
	by and_intro #unfold iff_def #elim and_elim.

setup rewrite iff_imp iff_imp_rev iff.refl iff.trans.
setup dual iff.sym.

lemma eq_iff: if eq: P = Q, ! prop P then P ⟺ Q;
	have! prop Q;
		fold(=) eq.
	unfold(=) eq.

lemma iff_eq_cong#cong: for f x, if f: f = f', x: x = x', ! prop (f x) then f x ⟺ f' x';
	apply eq_iff;
	unfold(=) f x.

