-----
## Notions for Sets or Types
-----
import Base.
fix (∈).

begin

theory Member:
	fix x A.
	assume closed: x ∈ A.
end

theory Unary:
	fix f A B.
	assume closed: x ∈ A ⟹ f x ∈ B.
end

theory Binary:
	fix f A B C.
	assume closed: x ∈ A ⟹ y ∈ B ⟹ f x y ∈ C.
end

theory Binder:
	fix ξ A B.
	assume closed: (∀x. x ∈ A ⟹ α.[x] ∈ B) ⟹ ξ A (x. α.[x]) ∈ B.
end

theory Magma:
	fix A (*).
	import Binary (*) A A A.
begin
	note! closed.
end

theory FunType:
	fix (→).
	assume fun_type_elim1: f ∈ A → B ⟹ ∀a. a ∈ A ⟹ f a ∈ B.
	assume fun_type_intro! for f A B, (∀a. a ∈ A ⟹ f a ∈ B) ⟹ f ∈ A → B.
begin
	note fun_type_elim: make_elim[of (f. f ∈ A → B) (f. ∀a. a ∈ A ⟹ f a ∈ B), OF fun_type_elim1].
end


theory Reflexive:
	fix A (≤).
	assume refl: x ∈ A ⟹ x ≤ x.
end

theory Symmetric:
	fix A (=).
	assume sym: x = y ⟹ x ∈ A ⟹ y ∈ A ⟹ y = x.
end

theory Transitive:
	fix A (≤).
	assume trans: x ≤ y ⟹ y ≤ z ⟹ x ∈ A ⟹ y ∈ A ⟹ z ∈ A ⟹ x ≤ z.
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

end

