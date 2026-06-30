import Membership.
fix Prop QTYPE (∀∈) (∃∈) (∧) (∨) (¬) (⟺).

assume Prop_type! Prop ∈ QTYPE.
assume allIn_type! if A ∈ QTYPE, ∀x. x ∈ A ⟹ P.[x] ∈ Prop then (∀x ∈ A. P.[x]) ∈ Prop.
assume exIn_type!  if A ∈ QTYPE, ∀x. x ∈ A ⟹ P.[x] ∈ Prop then (∃x ∈ A. P.[x]) ∈ Prop.

import FirstOrder;
	obtain false where ! false ∈ Prop;-- One can obtain false.
		- for thesis if assm;
			apply assm[of (∀P ∈ Prop. P)].
		.
	.

begin

theory Minimal:
	import Minimal;
begin
	lemma exIn_iff:
		if !A ∈ QTYPE, ! ∀x. x ∈ A ⟹ P.[x] ∈ Prop
		then (∃x ∈ A. P.[x]) ⟺ (∀Q ∈ Prop. (∀x ∈ A. P.[x] ⟹ Q) ⟹ Q);
		simp in.ex_def iff_iff_and;

		apply iff_intro;
		- if ex for Q if !, imp;
			apply in.ex_elim[OF ex];
			apply imp>0=.
		- if all;
			apply in.ex_intro;
			apply all>0=.
		.
end

theory Intuitionistic:
	import Intuitionistic;
		obtain false where ! false ∈ Prop, false_elim: if false then P;-- One can obtain false.
			- for thesis if assm;
				apply assm[of (∀P ∈ Prop. P)].
			.
		.
end

theory Classical:
	import Intuitionistic.
	import Classical.
end
