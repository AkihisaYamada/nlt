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
		lemma ex1_cong_iff(cong)
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
		lemma ex1_eq_iff: (∃!x. x = a ∧ P.[x]) ⟺ P.[a];
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
					by 1[OF ex1_imp_THE[OF ex1]].
				unfold zT;
				unfold 1[OF Px].
			.
		note eq_THE_intro: THE_eq_intro[THEN eq.sym].
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
		import AllExRel.
		fix (∃!<).
		assume ex1_def: (∃!x < a. P.[x]) = (∃x < a. P.[x] ∧ (∀y < a. P.[y] ⟹ y = x)).
	begin
		note(cong) all_cong ex_cong.
		lemma ex1_cong(cong)
			if eq: a = b, iff: ∀x. x < b ⟹ P.[x] ⟺ P'.[x] then (∃!x < a. P.[x]) ⟺ (∃!x < b. P'.[x]);
			simp ex1_def eq iff;.
		lemma ex1_intro1:
			for x a P if Px: P.[x], x: x < a, uniq: ∀y < a. P.[y] ⟹ y = x then ∃!x < a. P.[x];
			unfold ex1_def;
			by ex_intro1[of x] Px x uniq.
		lemma ex1_elim:
			if ex1: ∃!x < a. P.[x], imp: ∀x. x < a ⟹ P.[x] ⟹ (∀y < a. P.[y] ⟹ y = x) ⟹ Q then Q;
			apply ex1[unfold ex1_def, THEN ex_elim];
			unfold and_imp_iff_imp_imp;
			- for x;
				by imp[of x].
			.
		lemma ex1_eq_and_iff: for P then (∃!x < a. x = b ∧ P.[x]) ⟺ b < a ∧ P.[b];
			simp ex1_def and.left_assoc ex_eq_and_iff;
			by iff_intro.
		lemma ex1_eq_iff: (∃!x < a. x = b) ⟺ b < a;
			by ex1_eq_and_iff[of (x. true), simp].
	end

	theory TheRel:
		import Ex1Rel.
		fix THE.<.
		assume THE_intro: (∃!x < a. P.[x]) ⟹ P.[THE x < a. P.[x]].
		assume THE_in: (∃!x < a. P.[x]) ⟹ (THE x < a. P.[x]) < a.
	begin
		lemma THE_eq_intro: if ex1: ∃!y < a. P.[y], Px: P.[x], xa: x < a then (THE y < a. P.[y]) = x;
			apply ex1_elim[OF ex1];
			- for z if za: z < a, Pz: P.[z], 1: ∀y < a. P.[y] ⟹ y = z;
				note imp: 1[unfold all_def].
				have zT: (THE x < a. P.[x]) = z;
					by imp THE_intro ex1 THE_in.
				unfold zT;
				by Px xa #simp imp.
			.
		note eq_THE_intro: THE_eq_intro[THEN eq.sym].
	end

	theory AllEx1In:
		import Membership.
		import in: Ex1Rel (∈) (∀∈) (∃∈) (∃!∈).
	begin
		interpret Iff.
		note(cong) in.all_cong in.ex_cong in.ex1_cong.
		note(simp) in.ex_imp_iff.
	end

	theory AllEx1Sub:
		import AllEx1In.
		import sub: Ex1Rel (⊆) (∀⊆) (∃⊆) (∃!⊆).
	begin
		note(cong) sub.all_cong sub.ex_cong sub.ex1_cong.
		note(simp) sub.ex_imp_iff.
	end

	theory Prod: --- Product Class ---
		import AllEx1In.
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

	theory Currying:
		import Prod.
		assume curry: if f ∈ A × B → C then ∃f' ∈ A → B → C. ∀x ∈ A. ∀y ∈ A. f' x y = f (x,y).
	end

	theory UniqueChoice2:
		import Prod.
		import Fun.
		assume unique_choice2: for P A B C
			if ∀x ∈ A. ∀y ∈ B. ∃!z ∈ C. P.[x,y,z]
			then ∃f ∈ A → B → C. ∀x ∈ A. ∀y ∈ B. P.[x, y, f x y].
	end

	theory UniqueChoice:
		import Prod.
		import Fun.
		assume unique_choice: for P A B if ∀x ∈ A. ∃!y ∈ B. P.[x,y] then ∃f ∈ A → B. ∀x ∈ A. P.[x, f x].
	begin
		theory Currying:
			import Currying.
		begin
print.
			interpret UniqueChoice2;
				- for P A B C if all2_ex1;
					note(cong) eq_cong_meta[of P].
					apply unique_choice[of (((x,y),z). P.[x,y,z]) (A × B) C, THEN in.ex_elim];
					simp allIn_prod;
					- by all2_ex1.
					- for f if fty, f;
						apply curry[OF fty, THEN in.ex_elim];
						- for f' if f'ty, f'f;
							apply in.ex_intro1[OF f'ty];
							unfold f'f;
							- for x y;
								use f[of (x,y)];
								simp.
							.
						.
					.
				.
		end
	end

	theory UniqueChoice2:
		import UniqueChoice2.
	begin
		interpret Ex1.
		interpret UniqueChoice;
			- for P if all_ex1;
				note(cong) eq_cong_meta[of P].
				apply unique_choice2[of ((x,y,z). P.[y,z]), THEN ex_elim];
				simp;
				- by all_ex1.
				- for f if f;
					apply ex_intro1[of (f (,))];
					by f.
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
