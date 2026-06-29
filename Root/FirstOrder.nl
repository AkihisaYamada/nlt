import Membership.

fix Prop QTYPE (∧) (∨) (¬) (⟺) (∀∈) (∃∈) false.

import Propositional.

assume allIn_type! if A ∈ QTYPE, ∀x. x ∈ A ⟹ P.[x] ∈ Prop then (∀x ∈ A. P.[x]) ∈ Prop.
assume exIn_type! if A ∈ QTYPE, ∀x. x ∈ A ⟹ P.[x] ∈ Prop then (∃x ∈ A. P.[x]) ∈ Prop.

begin

extend Minimal begin

	note#simp in.ex_imp_iff_all.
	lemma exIn_cong:
		if eq: ∀x. x ∈ A ⟹ P.[x] ⟺ P'.[x],
			! A ∈ QTYPE, ! ∀x. x ∈ A ⟹ P.[x] ∈ Prop, ! ∀x. x ∈ A ⟹ P'.[x] ∈ Prop
		then (∃x ∈ A. P.[x]) ⟺ (∃x ∈ A. P'.[x]);
	-	apply iff_intro;
		- unfold[at 0] in.ex_def;
			simp eq;
			- for x;
				by in.ex_intro1[of x].
			.
		- unfold[at 0] in.ex_def;
			simp;
			- for x;
				by in.ex_intro1[of x] #simp eq.
			.
		.
	.
	lemma exIn_or_distrib:
		if ! A ∈ QTYPE, ! ∀x. x ∈ A ⟹ P.[x] ∈ Prop, ! ∀x. x ∈ A ⟹ Q.[x] ∈ Prop
		then (∃x ∈ A. P.[x] ∨ Q.[x]) ⟺ (∃x ∈ A. P.[x]) ∨ (∃x ∈ A. Q.[x]);
	-	note#cong in.all_cong_weak.
		simp iff_iff_and or_imp_iff in.all_and_distrib[dual];
		apply in.all_intro;
		- for x;
			by in.ex_intro1[of x].
		.
	.

end

extend Intuitionistic:
	import .Minimal.
end

extend Classical:
	import .Intuitionistic.
end
