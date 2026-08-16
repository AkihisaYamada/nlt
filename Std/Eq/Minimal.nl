---
# Type-Free Minimal Logic via Equality
---

import And, Or, Not, MinimalNot, IffViaAnd, Ex, Ex1.

begin

set simp (⟺).

instance base? Std.Minimal.

instance Ex1.And.
instance Ex1.Ex.

theory UniqueSuch :=
	fix (such).
	assume such_intro_ex1: if ∃!x. P.[x] then P.[such x. P.[x]].
begin

	lemma such_eq_intro: if ex1: ∃!y. P.[y], Px: P.[x] then (such y. P.[y]) = x;
		apply ex1_elim[OF ex1];
		- for z if Pz: P.[z], 1: ∀y. P.[y] ⟹ y = z;
			have zT: (such x. P.[x]) = z;
				by 1[OF such_intro_ex1[OF ex1]].
			unfold zT;
			unfold 1[OF Px].
		.
	note eq_such_intro: such_eq_intro[THEN eq.sym].

end

--- Hilbert's Choice operator ---
theory AnySuch :=
	fix (such).
	assume such_intro_ex: if ∃x. P.[x] then P.[such x. P.[x]].
begin

	instance UniqueSuch;
		- for P if ex1;
			by such_intro_ex[OF ex1[THEN ex1_imp_ex]].
		.

end

---
theory PairFoundation :=
	import Membership, Abbrev, UniqueSuch, Pair.
begin

	obtain If where
		if_then: if i, t ∈ A then If(i,t,e) = t,
		if_else: if i ⟹ t = e, e ∈ A then If(i,t,e) = e;
		- for thesis if assm;
			apply abbrev[of ((i,t,e). such r. (i ⟹ r = t) ∧ ((i ⟹ t = e) ⟹ r = e))];
			- for If if If;
				apply assm[of If];
				- if i: i, tA: t ∈ A then If(i,t,e) = t;
					apply If[dual, of A, THEN eq_elim1[of (x. x = t)]];
					- apply such_intro_ex1[of (x. x ∈ A)];
					  simp i[THEN iff_true] ex1_eq_and_iff all_eq_imp_iff tA[THEN iff_true].
					apply such_eq_intro;
					simp i[THEN iff_true] ex1_eq_and_iff.
				- if i0: i ⟹ t = e, eA: e ∈ A then If(i,t,e) = e;
					apply If[dual, of A, THEN eq_elim1[of (x. x = e)]];
					- apply such_intro_ex1[of (x. x ∈ A)];
						simp i0;
						- by ex1_intro1[of e].
						unfold imp_imp_commute; unfold all_eq_imp_iff;
						by eA.
					apply such_eq_intro;
					simp i0;
					unfold and.commute; unfold ex1_eq_and_iff.
				.
			.
		.
end
---