
fix (⊏) (∃!⊏).

assume ex1_intro1: for x a P if P.[x], ∀y. P.[y] ⟹ y ⊏ a ⟹ y = x, x ⊏ a then ∃!x ⊏ a. P.[x].
assume ex1_elim: if ∃!x ⊏ a. P.[x], ∀x. P.[x] ⟹ (∀y. P.[y] ⟹ y ⊏ a ⟹ y = x) ⟹ x ⊏ a ⟹ Q then Q.

begin

lemma ex1_intro: for a P
	if assm: ∀Q. (∀x. P.[x] ⟹ (∀y. P.[y] ⟹ y ⊏ a ⟹ y = x) ⟹ x ⊏ a ⟹ Q) ⟹ Q then ∃!x ⊏ a. P.[x];
	apply assm;
	- for x;
		apply ex1_intro1>0.
	.
lemma ex1_eq1: if ba: b ⊏ a then ∃!x ⊏ a. x = b;
	by ex1_intro1[of b] ba.

lemma ex1_eq2: if ba: b ⊏ a then ∃!x ⊏ a. b = x;
	by ex1_intro1[of b] ba #elim eq.sym.

lemma ex1_imp_eq:
	if ex1: ∃!x ⊏ a. P.[x], Px: P.[x], Py: P.[y], ! x ⊏ a, ! y ⊏ a then y = x;
	apply ex1_elim[OF ex1];
	- for z if Pz, eq, !;
		unfold eq[OF Px] eq[OF Py].
	.

extend ExRel begin

	lemma ex1_imp_ex: if ex1: ∃!x ⊏ a. P.[x] then ∃x ⊏ a. P.[x];
		apply ex1_elim[OF ex1];
		- for x; by ex_intro1[of x].
		.

end

theory UniqueSuchRel :=
	fix such_⊏.
	assume such_intro_ex1: if ∃!x ⊏ a. P.[x] then P.[such x ⊏ a. P.[x]].
	assume such_rel: if ∃!x ⊏ a. P.[x] then (such x ⊏ a. P.[x]) ⊏ a.
begin

	lemma such_eq_intro: if ex1: ∃!y ⊏ a. P.[y], Px: P.[x], ! x ⊏ a then (such y ⊏ a. P.[y]) = x;
		apply ex1_elim[OF ex1];
		- if Pz: P.[z], 1: ∀y. P.[y] ⟹ y ⊏ a ⟹ y = z, !;
			have zT: (such x ⊏ a. P.[x]) = z;
				by 1[OF such_intro_ex1[OF ex1]] such_rel[OF ex1].
			unfold zT;
			unfold 1[OF Px].
		.

	note eq_such_intro: such_eq_intro[THEN eq.sym].

end
