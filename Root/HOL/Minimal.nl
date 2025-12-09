import ..Minimal.

begin

lemma ex_iff:
if ! A ∈ TYPE, ! ∀x. x ∈ A ⟹ P.[x] ∈ PROP
then (∃x ∈ A. P.[x]) ⟺ (∀Q ∈ PROP. (∀x ∈ A. P.[x] ⟹ Q) ⟹ Q);
	apply iff_intro;
	if ex: ∃x ∈ A. P.[x];
		apply ex_elim[OF ex];
		for x if !x ∈ A, !P.[x];
			apply all_intro;
			for Q if !, all: ∀x ∈ A. P.[x] ⟹ Q;
				by all_elim1[of x, OF all].
			.
		.
	if all: ∀Q ∈ PROP. (∀x ∈ A. (P.[x] ⟹ Q)) ⟹ Q;
		apply all_elim1[OF all];
		- .
		- .
		- .
		apply all_intro;
		for x; by ex_intro1[of x].
		.
	.

theory ChoiceSet:
	fix A.
	assume choice: if ∀x ∈ X. ∃a ∈ A. P x a then ∃f ∈ X → A. ∀x ∈ X. P x (f x).
end

theory Choice:
	assume choice: if ∀x ∈ X. ∃a ∈ A. P x a then ∃f ∈ X → A. ∀x ∈ X. P x (f x).
end


