fix (∈) PROP EQTYPE.

import ..Prop.

assume eq_prop: if A ∈ EQTYPE, x ∈ A, y ∈ A then x = y ∈ PROP.

begin

interpret Membership.

theory Minimal:
	import Minimal.
begin
	theory If:
		fix (If) (,).
		assume if_then: P ⟹ If P (x,y) = x.
		assume if_else: ¬ P ⟹ If P (x,y) = y.
	begin
		interpret Pair;
			obtain fst where fst: fst (x,y) = x;
				for thesis if assm;
					by assm[of (If true)] #unfold if_then.
				.
			obtain snd where snd: snd (x,y) = y;
				for thesis if assm;
					by assm[of (If false)] not_false #unfold if_else.
				.
			by fst snd.
set print blast.
		lemma pair_eq_iff: (x,y) = (x',y') ⟺ x = x' ∧ y = y';
			apply iff_intro;
			if eq;
				apply and_intro;
				- by pair_eq_pair_imp1[OF eq].
				- by pair_eq_pair_imp2[OF eq].
				.
			.
	end
end

theory Intuitionistic:
	import ..Intuitionistic.
begin
	interpret Minimal.
end

theory Classical:
	import ..Classical.
begin
	interpret Intuitionistic.
end
