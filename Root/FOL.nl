import Base.
fix (∈) PROP TYPE (∀∈) (∃∈).
import Prop.

assume all_type!
if A ∈ TYPE, ∀x. x ∈ A ⟹ P.[x] ∈ PROP then (∀x ∈ A. P.[x]) ∈ PROP.

assume all_intro: for P A
if ∀x. x ∈ A ⟹ P.[x], A ∈ TYPE, ∀x. x ∈ A ⟹ P.[x] ∈ PROP
then ∀x ∈ A. P.[x].

assume all_elim1: for x P A
if ∀y ∈ A. P.[y], x ∈ A, A ∈ TYPE, ∀y. y ∈ A ⟹ P.[y] ∈ PROP
then P.[x].

assume ex_type!
if A ∈ TYPE, ∀x. x ∈ A ⟹ P.[x] ∈ PROP then (∃x ∈ A. P.[x]) ∈ PROP.

assume ex_intro1: for x P A
if P.[x], x ∈ A, ∀y. y ∈ A ⟹ P.[y] ∈ PROP, A ∈ TYPE
then ∃y ∈ A. P.[y].

assume ex_elim: for P A
if ∃x ∈ A. P.[x]
then ∀Q. (∀x. x ∈ A ⟹ P.[x] ⟹ Q) ⟹ A ∈ TYPE ⟹ (∀x. x ∈ A ⟹ P.[x] ∈ PROP) ⟹ Q ∈ PROP ⟹ Q.

begin

lemma all_elim:
	if all: ∀x ∈ A. P.[x]
	then ∀Q. ((∀x. x ∈ A ⟹ P.[x]) ⟹ Q) ⟹ A ∈ TYPE ⟹ (∀y. y ∈ A ⟹ P.[y] ∈ PROP) ⟹ Q;
	for Q if assm, !, !;
		apply assm;
		for x if !;
			apply all_elim1[OF all, of x].
		.
	.

lemma ex_intro:
if assm: ∀Q. (∀x. x ∈ A ⟹ P.[x] ⟹ Q) ⟹ Q ∈ PROP ⟹ Q,
	! A ∈ TYPE,
	! ∀x. x ∈ A ⟹ P.[x] ∈ PROP
then ∃x ∈ A. P.[x];
	apply assm;
	for x;
		by ex_intro1[of x].
	.
lemma ex_imp_all_imp:
if ex_imp: ∃x ∈ A. P.[x] ⟹ Q, all: ∀x ∈ A. P.[x],
	! A ∈ TYPE, ! Q ∈ PROP, ! ∀x. x ∈ A ⟹ P.[x] ∈ PROP
then Q;
	apply ex_elim[OF ex_imp];
	for x if !x ∈ A, imp: P.[x] ⟹ Q;
		by imp all_elim1[OF all].
	.

theory Sub:
	fix (⊆).
	assume sub_intro: if A ∈ TYPE, B ∈ TYPE, ∀x. x ∈ A ⟹ x ∈ B then A ⊆ B.
	assume sub_elim: if A ⊆ B, A ∈ TYPE, B ∈ TYPE then ∀x. x ∈ A ⟹ x ∈ B.
end

theory ChoiceOp:
	fix (SOME_IN).
	assume SOME: if ∃x ∈ A. P.[x], A ∈ TYPE then P.[SOME x ∈ A. P.[x]].
end

theory Eq:
	import Eq.
	assume eq_type: if A ∈ EQTYPE then A ∈ TYPE.
begin

	theory Ex1:
		fix (∃!∈).
		assume ex1_type: if A ∈ EQTYPE, ∀x. x ∈ A ⟹ P.[x] ∈ PROP then (∃!x ∈ A. P.[x]) ∈ PROP.
		assume ex1_imp_ex:
			if ∃!x ∈ A. P.[x], A ∈ EQTYPE, ∀x. x ∈ A ⟹ P.[x] ∈ PROP
			then ∃x ∈ A. P.[x].
		assume ex1_imp_unique:
			if ∃!x ∈ A. P.[x], A ∈ EQTYPE, ∀x. x ∈ A ⟹ P.[x] ∈ PROP
			then ∀x ∈ A. ∀y ∈ A. P.[x] ⟹ P.[y] ⟹ x = y.
		assume ex1_intro: for x
			if P.[x], ∀y ∈ A. P.[y] ⟹ y = x,
			   A ∈ EQTYPE, ∀x. x ∈ A ⟹ P.[x] ∈ PROP, x ∈ A
			then ∃!x ∈ A. P.[x].
	end

	theory UniqueChoiceOp:
		fix (∃!∈) THE_IN.
		import Ex1.
		assume THE_type:
			if A ∈ EQTYPE, ∀x. x ∈ A ⟹ P.[x] ∈ PROP
			then (THE x ∈ A. P.[x]) ∈ A.
		assume ex1_imp_THE:
			if ∃!x ∈ A. P.[x], A ∈ EQTYPE, ∀x. x ∈ A ⟹ P.[x] ∈ PROP
			then P.[THE x ∈ A. P.[x]].
	end

end
