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
	interpret subseteq: MetaPreorder (⊆);
		- by subseteq_intro.
		- if AB: A ⊆ B, BC: B ⊆ C;
			by subseteq_intro BC[THEN subseteq_elim1] AB[THEN subseteq_elim1].
		.
end


theory Reflexive A (⊑) :=
	assume refl#refl if x ∈ A then x ⊑ x.
end

theory Symmetric A (~) :=
	assume sym#dual if x ~ y, x ∈ A, y ∈ A then y ~ x.
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
	assume trans#trans if x ⊏ y, y ⊏ z, x ∈ A, y ∈ A, z ∈ A then x ⊏ z.
begin
	interpret Attractive;
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

	interpret Preorder A (~).

end

theory Monotone f A (<) (⊏) :=
	assume mono: if x < y, x ∈ A, y ∈ A then f x ⊏ f y.
end

theory Antitone f A (<) (⊏) :=
	assume cmono: if x ⊏ y, x ∈ A, y ∈ A then f y < f x.
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

theory Fun :=
	fix (fun).
	assume fun_app_elim: for P A if P.[(fun x. F.[x]) s], F.[s] ∈ A then P.[F.[s]].
begin

	lemma fun_app_intro: if P: P.[F.[s]], A: F.[s] ∈ A then P.[(fun x. F.[x]) s];
		apply fun_app_elim[for Z, of (y. P.[y] ⟹ Z), OF _ A P].

	lemma fun_indep_elim: if app: P.[(fun x. s) t], A: s ∈ A then P.[s];
		apply fun_app_elim[of P, OF app A].

end
