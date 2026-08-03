-----
# Notions for Sets or Types
-----
fix (∈).

begin

theory Member :=
	fix x A.
	assume closed! x ∈ A.
end

theory Binder :=
	fix ξ A B.
	assume closed: if ∀x. x ∈ A ⟹ F.[x] ∈ B then ξ A (x. F.[x]) ∈ B.
end

theory Unary :=
	fix f A B.
	assume closed: if x ∈ A then f x ∈ B.
end

theory To :=
	fix (→).
	assume to_elim1#intro[after 1] if f : A → B, x : A then f x : B.
begin
	---
	Type judgment of application can be reduced to that of the function,
	if one knows the type of the argument.
	---
	lemma app_in#intro[after 1] if [x : A, f : A → B] then f x : B.

	lemma to_elim: if f: f : A → B, assm: (∀x. x : A ⟹ f x : B) ⟹ Q then Q;
		use f; by assm.

end

theory Binary :=
	fix f A B C.
	assume closed: if x ∈ A, y ∈ B then f x y ∈ C.
end

theory Magma :=
	fix A (*).
	import Binary (*) A A A.
begin
	note! closed.
end

theory SubsetEq :=
	fix (⊆).
	assume subseteq_elim1: if A ⊆ B, x ∈ A then x ∈ B.
	assume subseteq_intro: if ∀x. x ∈ A ⟹ x ∈ B then A ⊆ B.
begin
	interpretation subseteq: MetaPreorder (⊆);
		- by subseteq_intro.
		- if AB: A ⊆ B, BC: B ⊆ C;
			by subseteq_intro BC[THEN subseteq_elim1] AB[THEN subseteq_elim1].
		.
end


theory Reflexive A (⊑) :=
	assume refl: if x ∈ A then x ⊑ x.
end

theory Symmetric A (~) :=
	assume sym: if x ~ y, x ∈ A, y ∈ A then y ~ x.
end

theory SemiAttractive A (⊏) :=
	assume attract: if x ⊏ y, y ⊏ x, y ⊏ z, x ∈ A, y ∈ A, z ∈ A then x ⊏ z.
end

theory DualAttractive A (⊏) :=
	assume dual_attract: if x ⊏ y, y ⊏ x, x ⊏ z, x ∈ A, y ∈ A, z ∈ A then y ⊏ z.
end

theory Attractive :=
	import SemiAttractive.
	import DualAttractive.
end

theory Transitive A (⊏) :=
	assume trans: if x ⊏ y, y ⊏ z, x ∈ A, y ∈ A, z ∈ A then x ⊏ z.
begin
	interpretation Attractive;
		- if xy: x ⊏ y, yx: y ⊏ x, yz: y ⊏ z;
			by trans[OF xy yz].
		- if xy: x ⊏ y, yx: y ⊏ x, xz: x ⊏ z;
			by trans[OF yx xz].
		.
end

theory Preorder :=
	import Reflexive.
	import Transitive A (⊑).
end

theory PartialEquivalence :=
	import Symmetric, Transitive A (~).
end

theory Tolerance A (~) :=
	import Reflexive A (~), Symmetric.
end

theory Equivalence A (~) :=
	import Tolerance, PartialEquivalence.
begin

	interpretation Preorder A (~).

end

theory CollectRel (⊏) :=
	fix Collect_⊏.
	assume Collect_intro: if x ⊏ a, P.[x] then x ∈ {x ⊏ a. P.[x]}.
	assume Collect_elim0: if x ∈ {x ⊏ a. P.[x]} then x ⊏ a.
	assume Collect_elim1: if x ∈ {x ⊏ a. P.[x]} then P.[x].
begin
	lemma Collect_elim: if x: x ∈ {x ⊏ a. P.[x]}, assm: x ⊏ a ⟹ P.[x] ⟹ Q then Q;
		apply assm[OF Collect_elim0[OF x] Collect_elim1[OF x]].
end
