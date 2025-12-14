import ..Classes.

begin

theory Image:
	fix (`).
	assume image_intro: if x ∈ A then f x ∈ f ` A.
	assume image_elim: if y ∈ f ` A then ∀P. (∀x. y = f x ⟹ x ∈ A ⟹ P) ⟹ P.
end

theory Pair:
	fix (×) (,) fst snd.
	assume pair_type! if x ∈ A, y ∈ B then (x,y) ∈ A × B.
	import Pair.
end
