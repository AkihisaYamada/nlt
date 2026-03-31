begin

interpret base? Root.TypeFree.

theory Minimal:
	import base? base.Minimal.-- Root.TypeFree.Minimal
begin

	interpret Eq.TypeSafeMinimal.-- Eq/TypeSafeMinimal

	lemma ex_eq_and_iff: (∃x. x = a ∧ P.[x]) ⟺ P.[a];
		note#cong eq_cong_meta[of P].
		apply iff_intro;
		-> if xa: x = a, Px: P.[x];
			by Px #fold xa.
		- if Pa: P.[a];
			by ex_intro1[of a] Pa.
		.
	lemma ex_eq_and_iff2: (∃x. a = x ∧ P.[x]) ⟺ P.[a];
		unfold iff_eq.commute;
		by ex_eq_and_iff.

	extend Ex1 begin
		lemma ex1_cong#cong
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
		lemma ex1_imp_eq: if ex1: ∃!x. P.[x], Py: P.[y], Pz: P.[z] then y = z;
			apply ex1_elim[OF ex1];
			- for x if Px, eq;
				unfold eq[OF Py] eq[OF Pz].
			.
		lemma ex1_imp_iff_eq: if ex1: ∃!x. P.[x], Px: P.[x] then P.[y] ⟺ x = y;
			apply iff_intro;
			- by ex1_imp_eq[OF ex1 Px].
			- if eq;
				note#cong eq_cong_meta[of P].
				by Px[unfold eq].
			.

		lemma ex1_eq_and_iff: (∃!x. x = a ∧ P.[x]) ⟺ P.[a];
			simp ex1_def and.left_assoc ex_eq_and_iff all_eq_imp_iff.

		extend The begin
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

	end

	extend AllRel begin -- extending Eq/TypeSafeMinimal/AllRel

		interpret base? base.AllRel.-- Root/Minimal/AllRel

		extend ExRel begin
			interpret base? base.ExRel.-- Root/Minimal/AllRel/ExRel

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
					apply ...ex_cong;-- TODO
					by iff_intro.
				unfold 1;
				unfold and.left_assoc ex_eq_and_iff.

			theory Ex1Rel:
				fix (∃!<).
				import Ex1.
				assume ex1_def: (∃!x < a. P.[x]) ⟺ (∃!x. x < a ∧ P.[x]).
			begin
				lemma ex1_cong#cong
					if eq: a = b, iff: ∀x. x < b ⟹ P.[x] ⟺ P'.[x] then (∃!x < a. P.[x]) ⟺ (∃!x < b. P'.[x]);
					simp ex1_def eq iff;.
				lemma ex1_intro1: for x a P
					if Px: P.[x], x: x < a, uniq: ∀y. y < a ⟹ P.[y] ⟹ y = x then ∃!x < a. P.[x];
					unfold ex1_def;
					by .ex1_intro1[of x] Px x uniq.

				lemma ex1_intro: for a P
					if assm: ∀Q. (∀x. x < a ⟹ P.[x] ⟹ (∀y. y < a ⟹ P.[y] ⟹ y = x) ⟹ Q) ⟹ Q
					then ∃!x < a. P.[x];
					unfold ex1_def;
					apply .ex1_intro;
					simp;
					apply assm>0=.

				lemma ex1_elim:
					if ex1: ∃!x < a. P.[x], imp: ∀x. x < a ⟹ P.[x] ⟹ (∀y. y < a ⟹ P.[y] ⟹ y = x) ⟹ Q then Q;
					apply ex1[unfold ex1_def, THEN .ex1_elim];
					unfold and_imp_iff_imp_imp;
					- for x;
						by imp[of x].
					.
				lemma ex1_imp_ex: (∃!x < a. P.[x]) ⟹ (∃x < a. P.[x]);
					unfold ex1_def ex_def;
					apply Ex1.ex1_imp_ex>0.
				lemma ex1_imp_eq: if ex1: ∃!x < a. P.[x], ! y < a, ! P.[y], ! z < a, ! P.[z] then y = z;
					apply Ex1.ex1_imp_eq[OF ex1[unfold ex1_def]].
				lemma ex1_imp_iff_eq: if ex1: ∃!x < a. P.[x], x: x < a, Px: P.[x], y: y < a then P.[y] ⟺ x = y;
					fold Ex1.ex1_imp_iff_eq[OF ex1[unfold ex1_def], rule, OF x Px, of y];
					by y.
				lemma ex1_eq_and_iff: for P then (∃!x < a. x = b ∧ P.[x]) ⟺ b < a ∧ P.[b];
					have 1: (∃!x < a. x = b ∧ P.[x]) ⟺ (∃!x. x = b ∧ x < a ∧ P.[x]);
						unfold ex1_def;
						apply Ex1.ex1_cong;
						by iff_intro.
					apply iff.trans[OF 1];
					simp and.left_assoc ex1_eq_and_iff.
				lemma ex1_eq_iff: (∃!x < a. x = b) ⟺ b < a;
					by ex1_eq_and_iff[of (x. true), simp].

				theory TheRel:
					fix TheLt.
					import The.
					assume THE_def: (THE x < a. P.[x]) = (THE x. x < a ∧ P.[x]).
				begin
					lemma THE_intro1: (∃!x < a. P.[x]) ⟹ P.[THE x < a. P.[x]];
						note#cong eq_cong_meta[of P].
						unfold ex1_def THE_def;
						by #elim The.THE_intro.
					lemma THE_intro0: (∃!x < a. P.[x]) ⟹ (THE x < a. P.[x]) < a;
						note#cong eq_cong_meta[of P].
						unfold ex1_def THE_def;
						by #elim The.THE_intro.
					lemma THE_eq_intro: if ex1: ∃!y < a. P.[y], Px: P.[x], xa: x < a then (THE y < a. P.[y]) = x;
						unfold THE_def;
						apply THE_eq_intro;
						- use ex1; simp ex1_def.
						by Px xa.
					note eq_THE_intro: THE_eq_intro[THEN eq.sym].
				end
			end
		end
	end

	theory Membership:
		import base? base.Membership.
	begin
		interpret Eq.Membership.

		theory AllIn:
			import base.AllIn.
		begin
			interpret in: AllRel (∈) (∀∈).
			note#cong in.all_cong.
			note#rule in.all_def.
			extend ExIn begin
				interpret in: in.ExRel (∃∈).
				note#cong in.ex_cong.
				note#elim in.ex_elim.
				note#simp in.ex_imp_iff.

				theory Ex1In:
					import Ex1.
					import in: in.Ex1Rel (∃!∈).
				begin
					note#cong in.ex1_cong.

					theory UniqueChoice:
						import Pair.
						assume unique_choice:
							if ∀x. ∃!y ∈ A.[x]. P.[x,y] then ∃f. ∀x. f x ∈ A.[x] ∧ P.[x, f x].
					begin
ctxt.
						interpret Abbrev;
							- for A if F: ∀x. F.[x] ∈ A.[x], assm: ∀f. (∀x. f x = F.[x]) ⟹ P then P;
								note#cong eq_cong_meta[of F].
								apply unique_choice[of A ((x,y). y = F.[x]), simp in.ex1_eq_iff, OF F, THEN ex_elim];
								- for f if f;
									apply assm[of f];
									- for x;
										use f[of x].
									.
								.
							.
					end

					theory UniqueChoiceCond:
						import Pair.
						assume unique_choice_cond:
							if ∀x. P.[x] ⟹ ∃!y ∈ A.[x]. Q.[x,y] then ∃f. ∀x. P.[x] ⟹ f x ∈ A.[x] ∧ Q.[x, f x].
					begin
						interpret UniqueChoice;
							- for A P if ex1;
								apply unique_choice_cond[of (x. true) (x. A.[x]) P, simp, OF ex1, THEN ex_elim];
								- for f if f;
									by ex_intro1[of f] f.
								.
							.
						interpret AbbrevCond;
							- for P A if F: ∀x. P.[x] ⟹ F.[x] ∈ A.[x] for Q if assm;
								note#cong eq_cong_meta[of F].
								apply unique_choice_cond[of P A ((x,y). y = F.[x]), simp in.ex1_eq_iff, OF F, THEN ex_elim];
								- for f if f;
									apply assm[of f];
									- for x if Px;
										use f[OF Px].
									.
								.
							.
					end

					theory TheIn:
						import The.
						fix TheIn.
						import in: in.TheRel TheIn.
					begin
						extend Lambda begin
							extend Pair begin
								interpret UniqueChoiceCond;
									- for P A Q if P_imp_ex1;
										apply ex_intro1[of (λx. THE y ∈ A.[x]. Q.[x,y])];
										- if Px: P.[x];
											note ex1: P_imp_ex1[OF Px].
											note! in.THE_intro0[OF ex1] in.THE_intro1[OF ex1].
											note#cong eq_cong_meta[of Q].
											unfold fun_app[of A].
										.
									.
							end
						end
					end
				end
			end
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
				note(cong) eq_cong_meta[of P].
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


