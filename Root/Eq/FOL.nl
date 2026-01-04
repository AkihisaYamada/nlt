---
# First-Order Logic with Equality

---

import Prop.
import ..FOL.

assume EQTYPE(intro 0) if A ∈ EQTYPE then A ∈ QTYPE.

begin

---
## Unique Existence
---
theory Ex1:
	fix (∃!∈).
	assume ex1_type!
		if A ∈ EQTYPE, ∀x. x ∈ A ⟹ P.[x] ∈ Prop
		then (∃!x ∈ A. P.[x]) ∈ Prop.
	assume ex1_imp_ex:
		if ∃!x ∈ A. P.[x], A ∈ EQTYPE, ∀x. x ∈ A ⟹ P.[x] ∈ Prop
		then ∃x ∈ A. P.[x].
	assume ex1_imp_unique:
		if ∃!x ∈ A. P.[x], A ∈ EQTYPE, ∀x. x ∈ A ⟹ P.[x] ∈ Prop
		then ∀x ∈ A. ∀y ∈ A. P.[x] ⟹ P.[y] ⟹ x = y.
	assume ex1_intro: for x
		if P.[x], ∀y ∈ A. P.[y] ⟹ y = x,
		   A ∈ QTYPE, ∀x. x ∈ A ⟹ P.[x] ∈ Prop, x ∈ A
		then ∃!x ∈ A. P.[x].
end

theory UniqueChoiceOp:
	fix (∃!∈) THE_IN.
	import Ex1.
	assume THE_type!
		if A ∈ EQTYPE, ∀x. x ∈ A ⟹ P.[x] ∈ Prop then (THE x ∈ A. P.[x]) ∈ A.
	assume ex1_imp_THE:
		if ∃!x ∈ A. P.[x], A ∈ EQTYPE, ∀x. x ∈ A ⟹ P.[x] ∈ Prop
		then P.[THE x ∈ A. P.[x]].
end

theory UniqueChoice:
	import Pair.
	import Ex1.
	assume unique_choice:
		if ∀x ∈ A. ∃!y ∈ B. P.[(x,y)],
			A ∈ EQTYPE, B ∈ EQTYPE, ∀x y. x ∈ A ⟹ y ∈ B ⟹ P.[(x,y)] ∈ Prop
		then for thesis if ∀f. f ∈ A → B ⟹ (∀x ∈ A. P.[(x, f x)]) ⟹ thesis then thesis.
end

theory Minimal:
	import FOL.Minimal.
	import Prop.Minimal.
begin

	theory Ex1:
		import Ex1.
	begin
		namespace iff:
			interpret iff.
			lemma ex1_iff: if A! A ∈ EQTYPE, ! ∀x. x ∈ A ⟹ P.[x] ∈ Prop
				then (∃!x ∈ A. P.[x]) ⟺ (∃x ∈ A. P.[x]) ∧ (∀x ∈ A. ∀y ∈ A. P.[x] ⟹ P.[y] ⟹ x = y);
			apply intro;
			- if ex1;
				by and.intro ex1_imp_ex[OF ex1] ex1_imp_unique[OF ex1].
			- if and;
				apply and.elim[OF and];
				- if ex, unique;
					apply ex.elim[OF ex];
					- for x if x!, Px;
						apply ex1_intro[of x, OF Px];
						apply all.intro;
						- for y if y!, Py;
							by all.elim1[OF all.elim1[OF unique y ! !] x ! !] Px Py.
						.
					.
				.
			.
			lemma ex1_cong: for A P
				if eq: ∀x. x ∈ A ⟹ P.[x] ⟺ Q.[x],
				   A! A ∈ EQTYPE, P! ∀x. x ∈ A ⟹ P.[x] ∈ Prop, Q! ∀x. x ∈ A ⟹ Q.[x] ∈ Prop
				then (∃!x ∈ A. P.[x]) ⟺ (∃!x ∈ A. Q.[x]);
			by #unfold ex1_iff[OF A] eq.

		end
	end

	theory UniqueChoice:
		import UniqueChoice.
	begin
		interpret .Ex1.
	end

	theory UniqueChoiceOp:
		import UniqueChoiceOp.
	begin
		interpret .Ex1.
	end

end

theory Intuitionistic:
	import Minimal.
	import Intuitionistic.
begin
	theory Ex1:
		import Ex1.
	end
	theory UniqueChoice:
		import UniqueChoice.
	end
	theory UniqueChoiceOp:
		import UniqueChoiceOp.
	end
end

theory Classical:
	import Classical.
	import Intuitionistic.
begin
	theory Ex1:
		import Ex1.
	end
	theory UniqueChoice:
		import UniqueChoice.
	end
	theory UniqueChoiceOp:
		import UniqueChoiceOp.
	end
end
