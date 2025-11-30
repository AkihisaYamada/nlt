fix true (∧) (∨).
import Prop.
import TypedTrue.
import TypedAnd.
import TypedOr.

begin

obtain false where ! false : prop;
	- for thesis, if assm;
		apply assm[of true].
	.

define[not] ¬P := P ⟹ false.

interpret TypedNot;
	by #unfold not_def.

define[iff] P ⟺ Q := (P ⟹ Q) ∧ (Q ⟹ P).

interpret ..MinimalPL;
	by and_intro #unfold iff_def #elim and_elim.

set rewrite iff_imp iff_imp_rev iff.refl iff.trans.
set dual iff.sym.

lemma eq_iff: if eq: P = Q, [P : prop] then P ⟺ Q;
	have! Q : prop;
		fold eq.
	unfold eq.

lemma iff_eq_cong#cong: for f x, if f: f = f', x: x = x', [f x : prop] then f x ⟺ f' x';
	apply eq_iff;
	unfold f x.

define Relation σ r := r : σ → σ → prop.

theory Relation:
	fix σ (≤).
	assume axiom: Relation σ (≤).
begin
	interpret ..Relation σ (≤);
		- by axiom[unfolded Relation_def, THEN fun_type_elim1, THEN fun_type_elim1].
		.
end


define EqType σ := Relation σ (=).

theory EqType:
	fix σ.
	assume axiom: EqType σ.
begin
	interpret eq: Relation σ (=);
		- by axiom[unfolded EqType_def].
		.
end
