begin

interpret base? Std.TypeFree.

theory Minimal :=
	fix false (∧) (∨) (¬) (⟺) (∃) (∃!).
	define true = (∀P. P ⟹ P).
	assume and_def: (P ∧ Q) = (∀R. (P ⟹ Q ⟹ R) ⟹ R).
	assume or_def: (P ∨ Q) = (∀R. (P ⟹ R) ⟹ (Q ⟹ R) ⟹ R).
	assume not_def: (¬ P) = (P ⟹ false).
	assume iff_def: (P ⟺ Q) = ((P ⟹ Q) ∧ (Q ⟹ P)).
	assume ex_def: (∃x. P.[x]) = (∀Q. (∀x. P.[x] ⟹ Q) ⟹ Q).
	assume ex1_def: (∃!x. P.[x]) = (∃x. P.[x] ∧ (∀y. P.[y] ⟹ y = x)).
begin

	interpret base? base.Minimal;-- Std/TypeFree/Minimal
		note #simp and_def iff_def not_def not_def or_def ex_def.
		- if PQ: P ⟹ Q, QP: Q ⟹ P then P ⟺ Q;
			by #elim PQ QP.
		- if iff: P ⟺ Q then P ⟹ Q;
			apply iff[simp].
		- if iff: P ⟺ Q then Q ⟹ P;
			apply iff[simp].
		- if or: P ∨ Q then ∀ R. (P ⟹ R) ⟹ (Q ⟹ R) ⟹ R;
			apply or[unfold or_def].
		- for x P if Px: P.[x] then ∃x. P.[x];
			unfold ex_def;
			- if all: ∀x. P.[x] ⟹ Q then Q;
				apply all[OF Px].
			.
		- if ex: ∃x. P.[x] for Q if all: ∀x. P.[x] ⟹ Q then Q;
			apply ex[unfold ex_def];
			- for x if Px: P.[x];
				by all[of x] Px.
			.
		retain true;
			by #simp true_def.
		.

	lemma eq_refl_iff#simp x = x ⟺ true;
		by iff_intro.

	interpret iff_eq: iff.MetaCommutative (=);
		by iff_intro[OF eq.sym eq.sym].

	lemma eq_imp_iff#cong? if eq: P = Q then P ⟺ Q;
		unfold[on (=)] eq.

	lemma all_eq_imp_iff: (∀x. x = a ⟹ P.[x]) ⟺ P.[a];
		apply iff_intro;
		- if all;
			apply all.
		- if Pa: P.[a], xa: x = a;
			by Pa #simp xa.
		.
	lemma ex_eq1: ∃x. x = a;
		apply ex_intro1[of a].
	lemma ex_eq2: ∃x. a = x;
		apply ex_intro1[of a].

	lemma ex1_intro1: for x P if Px: P.[x], u: ∀y. P.[y] ⟹ y = x then ∃!x. P.[x];
		unfold ex1_def;
		by ex_intro1[of x] Px u.

	lemma ex1_intro: if assm: ∀Q. (∀x. P.[x] ⟹ (∀y. P.[y] ⟹ y = x) ⟹ Q) ⟹ Q then ∃!x. P.[x];
		apply assm;
		- for x if Px;
			by ex1_intro1[OF Px].
		.
	lemma ex1_cong#cong
		if iff: ∀x. P.[x] ⟺ P'.[x] then (∃!x. P.[x]) ⟺ (∃!x. P'.[x]);
		unfold ex1_def iff.

	lemma ex1_elim: if ex1: ∃!x. P.[x], all: ∀x. P.[x] ⟹ (∀y. P.[y] ⟹ y = x) ⟹ Q then Q;
		apply ex1[unfold ex1_def, THEN ex_elim];
		- for x;
			by all[of x].
		.

	lemma ex1_eq1: ∃!x. x = a;
		apply ex1_intro1[of a].
	note#simp iff_true[OF ex1_eq1].

	lemma ex1_eq2: ∃!x. a = x;
		unfold iff_eq.commute.
	note#simp iff_true[OF ex1_eq2].

	lemma ex_eq_and_iff: (∃x. x = a ∧ P.[x]) ⟺ P.[a];
		apply iff_intro;
		-> if xa: x = a, Px: P.[x];
			by Px #fold xa.
		- if Pa: P.[a];
			by ex_intro1[of a] Pa.
		.
	lemma ex_eq_and_iff2: (∃x. a = x ∧ P.[x]) ⟺ P.[a];
		unfold iff_eq.commute;
		by ex_eq_and_iff.

	lemma ex1_imp_ex: if ex1: ∃!x. P.[x] then ∃x. P.[x];
		apply ex1_elim[OF ex1];
		- for x;
			by ex_intro1[of x].
		.
	lemma ex1_imp_eq: if ex1: ∃!x. P.[x], Py: P.[y], Pz: P.[z] then y = z;
		apply ex1_elim[OF ex1];
		- for x if Px, eq;
			unfold eq[OF Py] eq[OF Pz].
		.
	lemma ex1_imp_iff_eq: if ex1: ∃!x. P.[x], Px: P.[x] then P.[y] ⟺ x = y;
		apply iff_intro;
		- by ex1_imp_eq[OF ex1 Px].
		- if eq;
			by Px[unfold eq].
		.
	lemma ex1_eq_and_iff: (∃!x. x = a ∧ P.[x]) ⟺ P.[a];
		simp ex1_def and.left_assoc ex_eq_and_iff all_eq_imp_iff.

	theory UniqueChoiceOp :=
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

	extend Pair begin
		lemma pair_eq_pair#simp (x,y) = (x',y') ⟺ x = x' ∧ y = y';
			apply iff_intro;
			- if eq;
				by pair_eq_pair_elim1[OF eq] pair_eq_pair_elim2[OF eq].
			simp;
			- if x, y;
				simp x y.
			.
		lemma all_pair: (∀(x,y). P.[x,y]) ⟺ (∀x y. P.[x,y]);
			apply iff_intro;
			- if pair for x y;
				by pair[of (x,y),simp].
			- if xy;
				by xy.
			.
	end

	extend base? MetaRelation begin

		theory AllRel :=
			fix (∀⊏).
			assume all_def: (∀x ⊏ a. P.[x]) = (∀x. x ⊏ a ⟹ P.[x]).
		begin
			interpret base? base.AllRel;
				by #simp all_def.

			lemma all_cong:
				if ab: a = b, PQ: ∀x. x ⊏ b ⟹ P.[x] ⟺ Q.[x]
				then (∀x ⊏ a. P.[x]) ⟺ (∀x ⊏ b. Q.[x]);
				apply iff_intro;
				- if Pa;
					apply all_intro;
					by all_elim1[OF Pa, unfold ab] #fold PQ.
				- if Qb;
					apply all_intro;
					by all_elim1[OF Qb] #simp ab PQ.
				.
			lemma all_eq_imp_iff: (∀x ⊏ a. x = b ⟹ P.[x]) ⟺ (b ⊏ a ⟹ P.[b]);
				have 1: (∀x ⊏ a. x = b ⟹ P.[x]) ⟺ (∀x. x = b ⟹ x ⊏ a ⟹ P.[x]);
					unfold all_def;
					by iff_intro.
				unfold 1;
				unfold all_eq_imp_iff.

		end

		theory ExRel :=
			fix (∃⊏).
			assume ex_def: (∃x ⊏ a. P.[x]) = (∃x. x ⊏ a ∧ P.[x]).
		begin
			interpret base? base.ExRel; -- TypeFree/Minimal/MetaRelation/ExRel
				by #simp ex_def.
			lemma ex_cong:
				if ab: a = b, PQ: ∀x. x ⊏ b ⟹ P.[x] ⟺ Q.[x]
				then (∃x ⊏ a. P.[x]) ⟺ (∃x ⊏ b. Q.[x]);
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
			lemma ex_eq_iff: (∃x ⊏ a. x = b) ⟺ b ⊏ a;
				apply iff_intro;
				- if ex;
					apply ex_elim[OF ex];
					- if xa: x ⊏ a, xb: x = b;
						by xa[unfold xb].
					.
				- if ba: b ⊏ a;
					apply ex_intro1[OF ba].
				.
			lemma ex_eq_and_iff: (∃x ⊏ a. x = b ∧ P.[x]) ⟺ (b ⊏ a ∧ P.[b]);
				have 1: (∃x ⊏ a. x = b ∧ P.[x]) ⟺ (∃x. x = b ∧ x ⊏ a ∧ P.[x]);
					unfold ex_def;
					apply Minimal.ex_cong;
					by iff_intro.
				unfold 1;
				unfold and.left_assoc ex_eq_and_iff.
		end

		context AllRel begin--TODO: automate?
			extend .ExRel begin
				interpret base.ExRel.
			end
		end

		theory Ex1Rel :=
			fix (∃!⊏).
			assume ex1_def: (∃!x ⊏ a. P.[x]) = (∃!x. x ⊏ a ∧ P.[x]).
		begin
			lemma ex1_cong#cong
				if eq: a = b, iff: ∀x. x ⊏ b ⟹ P.[x] ⟺ P'.[x]
				then (∃!x ⊏ a. P.[x]) ⟺ (∃!x ⊏ b. P'.[x]);
				simp ex1_def eq iff.
			lemma ex1_intro1: for x a P
				if Px: P.[x], x: x ⊏ a, uniq: ∀y. y ⊏ a ⟹ P.[y] ⟹ y = x
				then ∃!x ⊏ a. P.[x];
				unfold ex1_def;
				by Minimal.ex1_intro1[of x] Px x uniq.

			lemma ex1_intro: for a P
				if assm: ∀Q. (∀x. x ⊏ a ⟹ P.[x] ⟹ (∀y. y ⊏ a ⟹ P.[y] ⟹ y = x) ⟹ Q) ⟹ Q
				then ∃!x ⊏ a. P.[x];
				unfold ex1_def;
				apply Minimal.ex1_intro;
				simp;
				apply assm>0=.

			lemma ex1_elim:
				if ex1: ∃!x ⊏ a. P.[x],
					imp: ∀x. x ⊏ a ⟹ P.[x] ⟹ (∀y. y ⊏ a ⟹ P.[y] ⟹ y = x) ⟹ Q
				then Q;
				apply ex1[unfold ex1_def, THEN .ex1_elim];
				unfold and_imp_iff_imp_imp;
				- for x;
					by imp[of x].
				.
			lemma ex1_imp_eq:
				if ex1: ∃!x ⊏ a. P.[x], ! y ⊏ a, ! P.[y], ! z ⊏ a, ! P.[z]
				then y = z;
				apply Minimal.ex1_imp_eq[OF ex1[unfold ex1_def]].
			lemma ex1_imp_iff_eq:
				if ex1: ∃!x ⊏ a. P.[x], x: x ⊏ a, Px: P.[x], y: y ⊏ a
				then P.[y] ⟺ x = y;
				fold Minimal.ex1_imp_iff_eq[OF ex1[unfold ex1_def], rule, OF x Px, of y];
				by y.
			lemma ex1_eq_and_iff: for P then (∃!x ⊏ a. x = b ∧ P.[x]) ⟺ b ⊏ a ∧ P.[b];
				have 1: (∃!x ⊏ a. x = b ∧ P.[x]) ⟺ (∃!x. x = b ∧ x ⊏ a ∧ P.[x]);
					unfold ex1_def;
					apply Minimal.ex1_cong;
					by iff_intro.
				apply iff.trans[OF 1];
				simp and.left_assoc ex1_eq_and_iff.
			lemma ex1_eq_iff: (∃!x ⊏ a. x = b) ⟺ b ⊏ a;
				by ex1_eq_and_iff[of (x. true), simp].

			theory SuchRel :=
				fix such.⊏ (such).
				assume such_def: (such x ⊏ a. P.[x]) = (such x. x ⊏ a ∧ P.[x]).
			end

			theory UniqueChoiceOpRel :=
				import UniqueChoiceOp.
				import SuchRel.
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
		context ExRel begin
			extend base? Ex1Rel begin
				lemma ex1_imp_ex: (∃!x ⊏ a. P.[x]) ⟹ (∃x ⊏ a. P.[x]);
					unfold ex1_def ex_def;
					apply Minimal.ex1_imp_ex>0.
			end
		end
	end

	theory Membership :=
		fix (∀∈) (∃∈) (∃!∈).
		interpret in: MetaRelation (∈).
		import in: in.AllRel (∀∈).
		import in: in.ExRel (∃∈).
		import in: in.Ex1Rel (∃!∈).
	begin

		interpret base.Membership.-- /Std/TypeFree/Membership

		note#cong in.all_cong.
		note#cong in.ex_cong.
		note#cong in.ex1_cong.

		theory Abbrev :=
			assume abbrev: ∀F A. ∃f. ∀x ∈ A. f x = F.[x].
		end

		theory AbbrevPoly :=-- Polymorphic Unary Abbreviation
			assume abbrev_poly: ∀F. ∃f. ∀A. ∀x ∈ A. f x = F.[x].
		end

		theory UniqueChoice :=
			import Pair.
			assume unique_choice: if ∀x ∈ A. ∃!y. P.[x,y] then ∃f. ∀x ∈ A. P.[x, f x].
		begin
			interpret Abbrev;
				- for F A;
					apply unique_choice[of A ((x,y). y = F.[x]), simp, THEN ex_elim];
					- for f if f;
						apply ex_intro1[of f];
						by f.
					.
				.
		end

		theory UniqueChoicePoly :=
			import Pair.
			assume unique_choice_poly:
				if ∀x. ∃!y. P.[x,y] then ∃f. ∀A. ∀x ∈ A. P.[x, f x].
		begin
			interpret AbbrevPoly;
				- for F;
					apply unique_choice_poly[of ((x,y). y = F.[x]), simp, THEN ex_elim];
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

end

theory Intuitionistic :=
	define false = (∀P. P).
	import Minimal.
begin
	interpret base.Intuitionistic;
		by #simp false_def.
end

theory Classical :=
	import .Intuitionistic.
	import DoubleNegation.
begin
	interpret base.Classical.
end


