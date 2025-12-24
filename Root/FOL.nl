---
# First-Order Logics

First-order logic (FOL) extends predicate logic with universal and existential
quantification over individuals.
We formulate FOL in a polymorphic manner: we do not assume a single type for individuals, but consider a class `QTYPE` of types that one is allowed to quantify over.
---

import Pred.

fix QTYPE (∀∈) (∃∈).

assume all_type!
	if A ∈ QTYPE, ∀x. x ∈ A ⟹ P.[x] ∈ Prop then (∀x ∈ A. P.[x]) ∈ Prop.

assume all_intro: for P A
	if ∀x. x ∈ A ⟹ P.[x], A ∈ QTYPE, ∀x. x ∈ A ⟹ P.[x] ∈ Prop
	then ∀x ∈ A. P.[x].

assume all_elim1: for x P A
	if ∀y ∈ A. P.[y], x ∈ A, A ∈ QTYPE, ∀y. y ∈ A ⟹ P.[y] ∈ Prop
	then P.[x].

assume ex_type!
	if A ∈ QTYPE, ∀x. x ∈ A ⟹ P.[x] ∈ Prop then (∃x ∈ A. P.[x]) ∈ Prop.

assume ex_intro1: for x P A
	if P.[x], x ∈ A, ∀y. y ∈ A ⟹ P.[y] ∈ Prop, A ∈ QTYPE
	then ∃y ∈ A. P.[y].

---
In the next ∃-elimination rule, it is crucial that `thesis` is not restricted to `Prop`.
In usual FOL foundation, type judgements do not depend on existence of objects,
---
assume ex_elim: for P A
	if ∃x ∈ A. P.[x]
	then ∀thesis. (∀x. x ∈ A ⟹ P.[x] ⟹ thesis) ⟹ A ∈ QTYPE ⟹ (∀x. x ∈ A ⟹ P.[x] ∈ Prop) ⟹ thesis.

begin

lemma all_elim: if all: ∀x ∈ A. P.[x]
	then for thesis if assm: (∀x. x ∈ A ⟹ P.[x]) ⟹ thesis, ! A ∈ QTYPE, ! (∀y. y ∈ A ⟹ P.[y] ∈ Prop)
	then thesis;
apply assm;
	for x if !;
	apply all_elim1[OF all, of x].
.

lemma ex_intro:
	if assm: ∀Q. (∀x. x ∈ A ⟹ P.[x] ⟹ Q) ⟹ Q ∈ Prop ⟹ Q,
		! A ∈ QTYPE,
		! ∀x. x ∈ A ⟹ P.[x] ∈ Prop
	then ∃x ∈ A. P.[x];
apply assm;
	for x;
	by ex_intro1[of x].
.

lemma ex_imp_all_imp:
	if ex_imp: ∃x ∈ A. P.[x] ⟹ Q, all: ∀x ∈ A. P.[x],
		! A ∈ QTYPE, ! Q ∈ Prop, ! ∀x. x ∈ A ⟹ P.[x] ∈ Prop
	then Q;
apply ex_elim[OF ex_imp];
	for x if !x ∈ A, imp: P.[x] ⟹ Q;
	by imp all_elim1[OF all].
.

theory Sub:
	fix (⊆).
	assume sub_intro: if A ∈ QTYPE, B ∈ QTYPE, ∀x. x ∈ A ⟹ x ∈ B then A ⊆ B.
	assume sub_elim: if A ⊆ B, A ∈ QTYPE, B ∈ QTYPE then ∀x. x ∈ A ⟹ x ∈ B.
end

theory ChoiceOp:
	fix (SOME_IN).
	assume SOME: if ∃x ∈ A. P.[x], A ∈ QTYPE then P.[SOME x ∈ A. P.[x]].
end

