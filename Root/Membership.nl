-----
## Notions for Sets or Types
-----
import Base.
fix (∈).

begin

theory Member:
	fix x A.
	assume closed! x ∈ A.
end

theory Binder:
	fix ξ A B.
	assume closed: if ∀x. x ∈ A ⟹ F.[x] ∈ B then ξ A (x. F.[x]) ∈ B.
end

theory Unary:
	fix f A B.
	assume closed: x ∈ A ⟹ f x ∈ B.
end

theory Binary:
	fix f A B C.
	assume closed: x ∈ A ⟹ y ∈ B ⟹ f x y ∈ C.
end

theory Magma:
	fix A (*).
	import Binary (*) A A A.
begin
	note! closed.
end

theory SubEq:
	fix (⊆).
	assume elim1: if A ⊆ B, x ∈ A then x ∈ B.
	assume intro: if ∀x. x ∈ A ⟹ x ∈ B then A ⊆ B.
begin
	interpret MetaPreorder (⊆);
		-; by intro.
		- if AB: A ⊆ B, BC: B ⊆ C;
			by intro BC[THEN elim1] AB[THEN elim1].
		.
end

theory Reflexive:
	fix A (≤).
	assume refl: if x ∈ A then x ≤ x.
end

theory Symmetric:
	fix A (=).
	assume sym: if x = y, x ∈ A, y ∈ A then y = x.
end

theory SemiAttractive:
	fix A (≤).
	assume attract: if x ≤ y, y ≤ x, y ≤ z, x ∈ A, y ∈ A, z ∈ A then x ≤ z.
end

theory DualAttractive:
	fix A (≤).
	assume dual_attract: if x ≤ y, y ≤ x, x ≤ z, x ∈ A, y ∈ A, z ∈ A then y ≤ z.
end

theory Attractive:
	import SemiAttractive.
	import DualAttractive.
end

theory Transitive:
	fix A (≤).
	assume trans: if x ≤ y, y ≤ z, x ∈ A, y ∈ A, z ∈ A then x ≤ z.
begin
	interpret Attractive;
		- if xy: x ≤ y, yx: y ≤ x, yz: y ≤ z, !, !, !;
			by trans[OF xy yz].
		- if xy: x ≤ y, yx: y ≤ x, xz: x ≤ z, !, !, !;
			by trans[OF yx xz].
		.
end

theory Preorder:
	fix A (≤).
	import Reflexive A (≤).
	import Transitive A (≤).
end

theory Tolerance:
	fix A (=).
	import Reflexive A (=).
	import Symmetric A (=).
end

theory PartialEquivalence:
	fix A (=).
	import Symmetric A (=).
	import Transitive A (=).
end

theory Equivalence:
	fix A (=).
	import Reflexive A (=).
	import Symmetric A (=).
	import Transitive A (=).
begin
	interpret Tolerance.
	interpret PartialEquivalence.
end

theory AllIn:
	fix (∀∈).
	assume allIn_intro! if ∀x. x ∈ A ⟹ P.[x] then ∀x ∈ A. P.[x].
	assume allIn_elim1: if ∀x ∈ A. P.[x], x ∈ A then P.[x].
begin
	lemma allIn_elim: if all: ∀x ∈ A. P.[x], imp: (∀x. x ∈ A ⟹ P.[x]) ⟹ Q then Q;
		by imp allIn_elim1[OF all].
end

theory ExIn:
	fix (∃∈).
	assume exIn_intro1: for x if P.[x], x ∈ A then ∃x ∈ A. P.[x].
	assume exIn_elim: if ∃x ∈ A. P.[x], ∀x. x ∈ A ⟹ P.[x] ⟹ Q then Q.
begin
	lemma exIn_intro: if assm: ∀Q. (∀x. x ∈ A ⟹ P.[x] ⟹ Q) ⟹ Q then ∃x ∈ A. P.[x];
		apply assm;
		- for x;
			by exIn_intro1[of x].
		.
end
