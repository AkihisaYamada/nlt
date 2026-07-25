import ..Membership.

begin

theory Antisymmetric A (⊑) :=
	assume antisym: if x ⊑ y, y ⊑ x, x ∈ A, y ∈ A then x = y.
begin
	interpret Attractive A (⊑);
		- by #simp[after 2] antisym.
		- by #simp[after 2] antisym[OF _ <].
		.
end

theory PseudoOrder :=
	import Reflexive, Antisymmetric.
end

theory Order :=
	import Preorder, Antisymmetric.
begin
	interpret PseudoOrder.
end

theory Injective f A :=
	assume injective: if x ∈ A, x' ∈ A, f x = f x' then x = x'.
end

theory Pair :=
	fix (,) fst snd.
	assume fst: if x ∈ A, y ∈ B then fst (x,y) = x.
	assume snd: if x ∈ A, y ∈ B then snd (x,y) = y.
end

---
## Membership with Restricted Quantifiers
---
theory QuantifyIn :=
	fix (∀∈) (∃∈) (∃!∈).
	import in: AllRel (∈) (∀∈).
	import in: ExRel (∈) (∃∈).
	import in: Ex1Rel (∈) (∃!∈).
begin

	note#cong in.all_cong.
	note#cong in.ex_cong.
	note#cong in.ex1_cong.

	theory AbbrevWeak :=
		assume abbrev_weak: ∀F A. ∃f. ∀x ∈ A. f x = F.[x].
	end

	theory Abbrev :=-- Polymorphic Unary Abbreviation
		assume abbrev: ∀F. ∃f. ∀A. ∀x ∈ A. f x = F.[x].
	end

	theory UniqueChoiceWeak :=
		import MetaPair.
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
