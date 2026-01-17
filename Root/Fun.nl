import Membership.

fix (→).
assume fun_elim1: if f ∈ A → B, a ∈ A then f a ∈ B.

begin

theory Unary:
	fix f A B.
	assume type: f ∈ A → B.
begin
	lemma closed: x ∈ A ⟹ f x ∈ B;
		by fun_elim1[OF type].
end

theory Binary:
	fix f A B C.
	assume type: f ∈ A → B → C.
begin
	lemma closed: x ∈ A ⟹ y ∈ B ⟹ f x y ∈ C;
		by type[THEN fun_elim1, THEN fun_elim1].
end

theory Magma:
	fix A (*).
	import Binary (*) A A A.
begin
	note! closed.
end
