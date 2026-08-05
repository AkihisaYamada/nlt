---
# Propositions

We fix a class `Prop` in which logical operators are closed.
---
import Membership.

fix Prop.
import imp: Magma Prop (⟹).

begin

note! imp.closed.

theory Relation A (⊏) :=
	import Binary (⊏) A A Prop.
begin

	note! closed.

end

theory PierceLaw :=
	assume pierce_law: if (P ⟹ Q) ⟹ P, P ∈ Prop, Q ∈ Prop then P.
end

theory True :=
	fix true.
	assume true_prop! true ∈ Prop.
	assume true_intro! true.
end

theory False :=
	fix false.
	assume false_prop! false ∈ Prop.
	assume false_elim: if false, P ∈ Prop then P.
begin

	interpretation True;
		obtain true where true_def: if P.[false ⟹ false] then P.[true];
			- for thesis if assm;
				apply assm[of (false ⟹ false)].
			.
		- apply true_def[of (x. x ∈ Prop)].
		- apply true_def[of (x. x)].
		.

end

theory AllRelStrict (⊏) (∀⊏) :=
	assume all_prop! if ∀x. x ⊏ A ⟹ P.[x] ∈ Prop then (∀x ⊏ A. P.[x]) ∈ Prop.
	assume all_intro: if ∀x. x ⊏ A ⟹ P.[x], ∀x. x ⊏ A ⟹ P.[x] ∈ Prop then ∀x ⊏ A. P.[x].
	assume all_elim1: for s if ∀x ⊏ A. P.[x], ∀x. x ⊏ A ⟹ P.[x] ∈ Prop, s ⊏ A then P.[s].
begin

	lemma all_elim:
		if all: ∀x ⊏ A. P.[x], assm: (∀x. x ⊏ A ⟹ P.[x]) ⟹ Q,
		   prop: ∀x. x ⊏ A ⟹ P.[x] ∈ Prop
		then Q;
		apply assm;
		- for x; by all_elim1[of x, OF all prop].
		.

end

theory ExRelStrict (⊏) (∀⊏) :=
	assume ex_prop! if ∀x. x ⊏ A ⟹ P.[x] ∈ Prop then (∃x ⊏ A. P.[x]) ∈ Prop.
	assume ex_intro1: if P.[x], x ⊏ A, ∀x. x ⊏ A ⟹ P.[x] ∈ Prop then ∃x ⊏ A. P.[x].
	assume ex_elim: if ∃x ⊏ A. P.[x], ∀x. P.[x] ⟹ x ⊏ A ⟹ Q, ∀x. x ⊏ A ⟹ P.[x] ∈ Prop then Q.
end
