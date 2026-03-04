begin

interpret base? ..TypeFree.

theory Minimal:
	import base? Minimal.
begin

	interpret TypeSafeMinimal.

	lemma ex_eq_and_iff: (∃x. x = a ∧ P.[x]) ⟺ P.[a];
		apply iff_intro;
		simp;
		note(cong) eq_cong_meta[of P].
		- if xa: x = a, Px: P.[x];
			by Px #fold xa.
		- if Pa: P.[a];
			by ex_intro1[of a] Pa.
		.

	theory Ex1:
		import Ex1.
	begin
		lemma ex1_cong(cong)
			if iff: ∀x. P.[x] ⟺ P'.[x] then (∃!x. P.[x]) ⟺ (∃!x. P'.[x]);
			unfold ex1_def iff.
		lemma ex1_elim: if ex1: ∃!x. P.[x], all: ∀x. P.[x] ⟹ (∀y. P.[y] ⟹ y = x) ⟹ Q then Q;
			apply ex1[unfold ex1_def, THEN ex_elim];
			- for x;
				by all[of x].
			.
		lemma ex1_imp_ex: if ex1: ∃!x. P.[x] then ∃x. P.[x];
			apply ex1_elim[OF ex1];
			- for x;
				by ex_intro1[of x].
			.
		lemma ex1_eq_and_iff: (∃!x. x = a ∧ P.[x]) ⟺ P.[a];
			simp ex1_def and.left_assoc ex_eq_and_iff all_eq_imp_iff.
	end

	theory The:
		import The.
	begin
		interpret .Ex1.
		lemma THE_eq_intro: if ex1: ∃!y. P.[y], Px: P.[x] then (THE y. P.[y]) = x;
			apply ex1_elim[OF ex1];
			- for z if Pz: P.[z], 1: ∀y. P.[y] ⟹ y = z;
				have zT: (THE x. P.[x]) = z;
					by 1[OF THE_intro[OF ex1]].
				unfold zT;
				unfold 1[OF Px].
			.
		note eq_THE_intro: THE_eq_intro[THEN eq.sym].
	end

	theory Abbrev:-- Restricted Unary Abbreviation
		import Membership.
		assume abbrev_cond: for P F A
			if ∀x. P.[x] ⟹ F.[x] ∈ A then ∃f. ∀x. P.[x] ⟹ f x = F.[x].
	begin
		lemma abbrev:
			if ty: ∀x. F.[x] ∈ A then ∃f. ∀x. f x = F.[x];
			by abbrev_cond[of (x. true) F A, simp, OF ty].
	end

	theory ExRel:
		import base.ExRel.
	begin
		lemma ex_cong:
			if ab: a = b, PQ: ∀x. x < b ⟹ P.[x] ⟺ Q.[x]
			then (∃x < a. P.[x]) ⟺ (∃x < b. Q.[x]);
		-	apply iff_intro;
			- if Pa;
				apply ex_elim[OF Pa];
				- for x;
					by ex_intro1[of x] #simp ab PQ[dual].
				.
			- if Qb;
				apply ex_elim[OF Qb];
				- for x;
					by ex_intro1[of x] #simp ab PQ.
				.
			.
		.
		lemma ex_eq_iff: (∃x < a. x = b) ⟺ b < a;
			apply iff_intro;
			- if ex;
				apply ex_elim[OF ex];
				- if xa: x < a, xb: x = b;
					by xa[unfold xb].
				.
			- if ba: b < a;
				apply ex_intro1[OF ba].
			.
		lemma ex_eq_and_iff: (∃x < a. x = b ∧ P.[x]) ⟺ (b < a ∧ P.[b]);
			have 1: (∃x < a. x = b ∧ P.[x]) ⟺ (∃x. x = b ∧ x < a ∧ P.[x]);
				unfold ex_def;
				apply base.ex_cong;
				by iff_intro.
			unfold 1;
			unfold and.left_assoc ex_eq_and_iff.

	end

	theory AllExRel:
		import AllExRel.
	begin
		interpret AllRel.
		interpret .ExRel.
	end

	theory Ex1Rel:
		import Ex1.
		fix (<) (∃!<).
		assume ex1_def: (∃!x < a. P.[x]) = (∃!x. x < a ∧ P.[x]).
	begin
		lemma ex1_cong(cong)
			if eq: a = b, iff: ∀x. x < b ⟹ P.[x] ⟺ P'.[x] then (∃!x < a. P.[x]) ⟺ (∃!x < b. P'.[x]);
			simp ex1_def eq iff;.
		lemma ex1_intro1:
			for x a P if Px: P.[x], x: x < a, uniq: ∀y. y < a ⟹ P.[y] ⟹ y = x then ∃!x < a. P.[x];
			unfold ex1_def;
			by .ex1_intro1[of x] Px x uniq.
		lemma ex1_elim:
			if ex1: ∃!x < a. P.[x], imp: ∀x. x < a ⟹ P.[x] ⟹ (∀y. y < a ⟹ P.[y] ⟹ y = x) ⟹ Q then Q;
			apply ex1[unfold ex1_def, THEN .ex1_elim];
			unfold and_imp_iff_imp_imp;
			- for x;
				by imp[of x].
			.
		lemma ex1_eq_and_iff: for P then (∃!x < a. x = b ∧ P.[x]) ⟺ b < a ∧ P.[b];
			have 1: (∃!x < a. x = b ∧ P.[x]) ⟺ (∃!x. x = b ∧ x < a ∧ P.[x]);
				unfold ex1_def;
				apply Ex1.ex1_cong;
				by iff_intro.
			apply iff.trans[OF 1];
			simp and.left_assoc ex1_eq_and_iff.
		lemma ex1_eq_iff: (∃!x < a. x = b) ⟺ b < a;
			by ex1_eq_and_iff[of (x. true), simp].
	end

	theory TheRel:
		import The.
		import Ex1Rel.
		fix _TheLt.
		assume THE_def: (THE x < a. P.[x]) = (THE x. x < a ∧ P.[x]).
	begin
		lemma THE_intro: (∃!x < a. P.[x]) ⟹ P.[THE x < a. P.[x]];
			note(cong) eq_cong_meta[of P].
			unfold Ex1Rel.ex1_def THE_def;
			by #elim The.THE_intro.
		lemma THE_rel: (∃!x < a. P.[x]) ⟹ (THE x < a. P.[x]) < a;
			note(cong) eq_cong_meta[of P].
			unfold Ex1Rel.ex1_def THE_def;
			by #elim The.THE_intro.
		lemma THE_eq_intro: if ex1: ∃!y < a. P.[y], Px: P.[x], xa: x < a then (THE y < a. P.[y]) = x;
			unfold THE_def;
			apply THE_eq_intro;
			- use ex1; simp ex1_def.
			by Px xa.
		note eq_THE_intro: THE_eq_intro[THEN eq.sym].
	end

	theory AllExIn:
		import AllExIn.
	begin
		interpret Iff.
		interpret in: AllExRel (∈) (∀∈) (∃∈).
		note(cong) in.all_cong in.ex_cong.
		note(rule) in.all_def.
		note(simp) in.ex_imp_iff.
	end

	theory Ex1In:
		import Ex1.
		fix (∈) (∃!∈).
		import in: Ex1Rel;
			instantiate (<) := (∈), (∃!<) := (∃!∈).
			.
	begin
		note(cong) in.ex1_cong.
	end

	theory TheIn:
		import The.
		fix (∈) (∃!∈) _TheIn.
		import in: TheRel;
			instantiate (<) := (∈), (∃!<) := (∃!∈), _TheLt := _TheIn.
			.
	begin
		interpret Ex1In.
	end

	theory AllExSub:
		import AllExIn.
		import sub: AllExRel (⊆) (∀⊆) (∃⊆).
	begin
		note(cong) sub.all_cong sub.ex_cong.
		note(simp) sub.ex_imp_iff.
	end

	theory Prod: --- Product Class ---
		import AllExIn.
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
			note(cong) eq_cong_meta[of P].
			simp in.all_def imp_all_iff in_prod_iff;
			apply iff_intro;
			- if l for x y if x, y;
				by l[OF x y eq.refl].
			- if r for p x y if x, y, p;
				by r x y #simp p.
			.
	end

	theory Abbrev2:-- Restricted Binary Abbreviation
		import Pair.
		import Membership.
		assume abbrev2_cond: for P F A
			if ∀x y. P.[x,y] ⟹ F.[x,y] ∈ A then ∃f. ∀x y. P.[x,y] ⟹ f x y = F.[x,y].
	begin
		interpret Abbrev;
			- for P F A if ty;
				note(cong) eq_cong_meta[of P] eq_cong_meta[of F].
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

	theory UniqueChoice:
		import Pair.
		import AllExIn.
		import Ex1In.
		assume unique_choice_cond: for P Q A
			if ∀x. P.[x] ⟹ ∃!y ∈ A. Q.[x,y] then ∃f. ∀x. P.[x] ⟹ f x ∈ A ∧ Q.[x, f x].
	begin
		lemma unique_choice: for P A B
			if ex1: ∀x ∈ A. ∃!y ∈ B. P.[x,y] then ∃f. ∀x ∈ A. f x ∈ B ∧ P.[x, f x];
			unfold in.all_def;
			apply unique_choice_cond;
			by ex1[rule].
		interpret Abbrev;
			- if F: ∀x. P.[x] ⟹ F.[x] ∈ A then ∃f. ∀x. P.[x] ⟹ f x = F.[x];
				note(cong) eq_cong_meta[of F].
				apply unique_choice_cond[of P ((x,y). y = F.[x]), simp in.ex1_eq_iff, OF F, THEN ex_elim];
				- for f if f;
					apply ex_intro1[of f];
					- for x if Px;
						use f[OF Px].
					.
				.
			.
	end

	theory UniqueChoice2:
		import Pair.
		import AllExIn.
		import Ex1In.
		assume unique_choice2_cond: for P Q A
			if ∀x y. P.[x,y] ⟹ ∃!z ∈ A. Q.[x,y,z]
			then ∃f. ∀x y. P.[x,y] ⟹ f x y ∈ A ∧ Q.[x, y, f x y].
	begin
		interpret UniqueChoice;
			- for P Q A if ex1;
				note(cong) eq_cong_meta[of P] eq_cong_meta[of Q].
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
				note(cong) eq_cong_meta[of F].
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

theory Intuitionistic:
	import base.Intuitionistic.
begin
	interpret .Minimal.
end

theory Classical:
	import base.Classical.
begin
	interpret .Intuitionistic.
end

theory Fun:
	import Membership.
	fix FUN.
	assume FUN: if F.[x] ∈ A then FUN A (x. F.[x]) x = F.[x].
end

