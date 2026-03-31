
import Base.

fix (<) (∀<).
assume all_intro! if ∀x. x < a ⟹ P.[x] then ∀x < a. P.[x].
assume all_elim1: for x if ∀y < a. P.[y], x < a then P.[x].

begin

lemma all_elim: if all: ∀x < a. P.[x], imp: (∀x. x < a ⟹ P.[x]) ⟹ Q then Q;
	by imp all_elim1[OF all].
