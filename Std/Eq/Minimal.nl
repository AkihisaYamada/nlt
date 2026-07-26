---
# Type-Free Minimal Logic via Equality
---

import And, Or, Not, MinimalNot, !IffViaAnd, Ex.

begin

interpret base? Std.Minimal.


theory PairFoundation :=
	import Membership, Abbrev, Ex1, UniqueSuch, MetaPair.
begin

	interpret Ex1.And.

	obtain If where
		if_then: if i, t ∈ A then If(i,t,e) = t,
		if_else: if i ⟹ t = e, e ∈ A then If(i,t,e) = e;
		- for thesis if assm;
			apply abbrev[of ((i,t,e). such r. (i ⟹ r = t) ∧ ((i ⟹ t = e) ⟹ r = e))];
			- for If if If;
				apply assm[of If];
				- if i: i, tA: t ∈ A then If(i,t,e) = t;
					apply If[dual, of A, THEN eq_elim[of (x. x = t)]];
					- apply such_intro_ex1[of (x. x ∈ A)];
					  simp i[THEN iff_true] ex1_eq_and_iff all_eq_imp_iff tA[THEN iff_true].
					apply such_eq_intro;
					simp i[THEN iff_true] ex1_eq_and_iff.
				- if i0: i ⟹ t = e, eA: e ∈ A then If(i,t,e) = e;
					apply If[dual, of A, THEN eq_elim[of (x. x = e)]];
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
## Membership with Restricted Quantifiers

In this theory, we "define" restricted quantifier via equality.
This has an advantage that 
---
theory RestrictedQuantifiers :=
	fix (∀∈) (∃∈) (∃!∈).
	import in: AllRel (∈) (∀∈).
	import in: ExRel (∈) (∃∈).
	import in: Ex1Rel (∈) (∃!∈).
begin

	note#cong in.all_cong.
	note#cong in.ex_cong.
	note#cong in.ex1_cong.

	interpret Eq.Membership.-- /Std/Eq/Membership

	interpret base? base.Membership;-- Std/Minimal/Membership.
		goals.
		by #simp in.all_def in.ex_def.


	theory AbbrevWeak :=
		assume abbrev_weak: ∀F A. ∃f. ∀x ∈ A. f x = F.[x].
	end

	theory Abbrev :=-- Polymorphic Unary Abbreviation
		assume abbrev: ∀F. ∃f. ∀A. ∀x ∈ A. f x = F.[x].
	end

	theory UniqueChoiceWeak :=
		import Pair.
		assume unique_choice_weak: if ∀x ∈ A. ∃!y. P.[x,y] then ∃f. ∀x ∈ A. P.[x, f x].
	begin

		interpret AbbrevWeak;
			- for F A;
				apply unique_choice_weak[of A ((x,y). y = F.[x]), simp, THEN ex_elim];
				- for f if f;
					apply ex_intro1[of f];
					by f.
				.
			.
	end

	theory UniqueChoice :=
		import Pair.
		assume unique_choice:
			if ∀x. ∃!y. P.[x,y] then ∃f. ∀A. ∀x ∈ A. P.[x, f x].
	begin
		interpret Abbrev;
			- for F;
				apply unique_choice[of ((x,y). y = F.[x]), simp, THEN ex_elim];
				- for f if f;
					apply ex_intro1[of f];
					by f.
				.
			.
	end

----- maybe not useful
	theory Pair:
		import Pair.
	begin

		theory Abbrev2:-- Restricted Binary Abbreviation
			assume abbrev2_cond: for P F A
				if ∀x y. P.[x,y] ⟹ F.[x,y] ∈ A then ∃f. ∀x y. P.[x,y] ⟹ f x y = F.[x,y].
		begin
			interpret Abbrev;
				- for P F A if ty;
					apply abbrev2_cond[of ((x,y). P.[y]) ((x,y). F.[y]), simp, OF ty, THEN ex_elim];
					- for f if f;
						apply ex_intro1[for x, of (f x)];
						unfold f.
					.
				.
			--- requires functional types!
			lemma abbrev3: for P F A if ty: ∀x y z. F.[x,y,z] ∈ A then ∃f. ∀x y z. f x y z = F.[x,y,z];
				apply abbrev2[of (((x,y),z). F.[x,y,z])];
				- for f2 if (simp);
					apply abbrev2[of ((x,y). f2 (x,y))];
					- for f3 if (simp);
						apply ex_intro;
						- for thesis if assm;
							by assm[of f3] #cong eq.cong_meta[of F].
						.
					.
				.
			---
		end


		theory UniqueChoice2:
			import AllIn.
			import ExIn.
			import Ex1In.
			import Pair.
			assume unique_choice2_cond: for P Q A
				if ∀x y. P.[x,y] ⟹ ∃!z ∈ A. Q.[x,y,z]
				then ∃f. ∀x y. P.[x,y] ⟹ f x y ∈ A ∧ Q.[x, y, f x y].
		begin
			interpret UniqueChoice;
				- for P Q A if ex1;
					apply unique_choice2_cond[of ((x,y). P.[y]) ((x,y,z). Q.[y,z]), simp, OF ex1, THEN ex_elim];
					- for f if f;
						apply ex_intro1[for x, of (f x)];
						by f.
					.
				.
			lemma curry_cond: for f if ty: ∀x y. P.[x,y] ⟹ f (x,y) ∈ A then ∃f'. ∀x y. P.[x,y] ⟹ f' x y = f (x,y);
				apply unique_choice2_cond[of P ((x,y,z). z = f (x,y)) A, simp in.ex1_eq_iff, OF ty, THEN ex_elim];
				- for f' if f';
					apply ex_intro1[of f'];
					- for x y if Pxy: P.[x,y];
						use f'[OF Pxy].
					.
				.
			lemma curry: for f if ty: ∀x y. f (x,y) ∈ A then ∃f'. ∀x y. f' x y = f (x,y);
				by curry_cond[of f (_. true), simp, OF ty].

			interpret Abbrev2;
				- if F: ∀x y. P.[x,y] ⟹ F.[x,y] ∈ A then ∃f. ∀x y. P.[x,y] ⟹ f x y = F.[x,y];
					apply unique_choice2_cond[of P ((x,y,z). z = F.[x,y]), simp in.ex1_eq_iff, OF F, THEN ex_elim];
					- for f if f;
						apply ex_intro1[of f];
						- for x y if Pxy;
							use f[OF Pxy].
						.
					.
				.
		end

	end

	theory Prod: --- Product Class ---
		import AllIn.
		import ExIn.
		import .Pair.
		fix (×).
		assume in_prod_iff: p ∈ A × B ⟺ (∃x ∈ A. ∃y ∈ B. p = (x,y)).
	begin
		lemma pair_in_prod_iff(simp) (x,y) ∈ A × B ⟺ x ∈ A ∧ y ∈ B;
			apply iff_intro;
			simp in_prod_iff;
			- if x': x' ∈ A, y': y' ∈ B, xx': x = x', yy': y = y';
				by x' y' #simp xx' yy'.
			- if x: x ∈ A, y: y ∈ B;
				by in.ex_intro1[OF x] in.ex_intro1[OF y].
			.
		lemma pair_in_prod: if ! x ∈ A, ! y ∈ B then (x,y) ∈ A × B.
		lemma allIn_prod: (∀p ∈ A × B. P.[p]) ⟺ (∀x ∈ A. ∀y ∈ B. P.[x,y]);
			simp in.all_def imp_all_iff in_prod_iff;
			apply iff_intro;
			- if l for x y if x, y;
				by l[OF x y eq.refl].
			- if r for p x y if x, y, p;
				by r x y #simp p.
			.
	end
-----

end

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

	extend base? MetaRelation begin

		theory SuchRel :=
			import base.Ex1Rel.
			import base.SuchRel.
		begin

			lemma such_intro1_ex1: (∃!x ⊏ a. P.[x]) ⟹ P.[such x ⊏ a. P.[x]];
				unfold ex1_def such_def;
				by #elim such_intro_ex1.

			lemma such_intro0_ex1: (∃!x ⊏ a. P.[x]) ⟹ (such x ⊏ a. P.[x]) ⊏ a;
				unfold ex1_def such_def;
				by #elim such_intro_ex1.

			lemma such_eq_intro: if ex1: ∃!y ⊏ a. P.[y], Px: P.[x], xa: x ⊏ a then (such y ⊏ a. P.[y]) = x;
				unfold such_def;
				apply such_eq_intro;
				- use ex1; simp ex1_def.
				by Px xa.

			note eq_such_intro: such_eq_intro[THEN eq.sym].

		end

	end

	theory Membership :=
		import ..Membership.
		interpret in: .MetaRelation (∈).
		import in: in.SuchRel (∃∈) (such.∈).
	end

--- Hilbert's Choice operator ---
theory AnySuch :=
	fix (such).
	assume such_intro_ex: if ∃x. P.[x] then P.[such x. P.[x]].
begin

	interpret UniqueSuch;
		- for P if ex1;
			by such_intro_ex[OF ex1[THEN ex1_imp_ex]].
		.

end
