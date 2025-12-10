import ..Prop.
begin

import Classes.

theory Minimal:
	import ..Minimal.
begin
	theory If:
		fix (If) (,).
		assume if_then: P ⟹ If P (x,y) = x.
		assume if_else: ¬ P ⟹ If P (x,y) = y.
	begin
		interpret Pair;
			obtain fst where fst: fst (x,y) = x;
				for thesis if assm;
					by assm[of (If true)].
				.
			obtain snd where snd: snd (x,y) = y;
				for thesis if assm;
					by assm[of (If false)].
				.
			.
		lemma pair_eq_iff: (x,y) = (x',y') ⟺ x = x' ∧ y = y';
			apply iff_intro;
			- by #elim pair_eq_imp1.
			- by #elim pair_eq_imp2.
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
