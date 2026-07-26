---
# Type-Free Unique Existence
---
fix (∃!).
assume ex1_intro1: for x P if P.[x], ∀y. P.[y] ⟹ y = x then ∃!x. P.[x].
assume ex1_elim: if ∃!x. P.[x], ∀x. P.[x] ⟹ (∀y. P.[y] ⟹ y = x) ⟹ Q then Q.

begin

lemma ex1_intro: if assm: ∀Q. (∀x. P.[x] ⟹ (∀y. P.[y] ⟹ y = x) ⟹ Q) ⟹ Q then ∃!x. P.[x];
	apply assm;
	- for x;
		apply ex1_intro1>0.
	.

lemma ex1_eq1: ∃!x. x = a;
	apply ex1_intro1[of a].

lemma ex1_eq2: ∃!x. a = x;
	apply ex1_intro1[of a];
	by #elim eq.sym.

lemma ex1_imp_eq: if ex1: ∃!x. P.[x], Px: P.[x], Py: P.[y] then y = x;
	apply ex1_elim[OF ex1];
	- for z if Pz, eq;
		unfold eq[OF Px] eq[OF Py].
	.

extend Ex begin

	lemma ex1_imp_ex: if ex1: ∃!x. P.[x] then ∃x. P.[x];
		apply ex1_elim[OF ex1];
		- for x; by ex_intro1[of x].
		.

end

theory UniqueSuch :=
	fix (such).
	assume such_intro1_ex1: if ∃!x. P.[x] then P.[such x. P.[x]].
begin

	lemma such_intro_ex1: for Q if ex1: ∃!x. P.[x], all: ∀x. P.[x] ⟹ Q.[x] then Q.[such x. P.[x]];
		apply all;
		by such_intro1_ex1[OF ex1].

	lemma such_eq_intro: if ex1: ∃!y. P.[y], Px: P.[x] then (such y. P.[y]) = x;
		apply ex1_elim[OF ex1];
		- for z if Pz: P.[z], 1: ∀y. P.[y] ⟹ y = z;
			have zT: (such x. P.[x]) = z;
				by 1[OF such_intro1_ex1[OF ex1]].
			unfold zT;
			unfold 1[OF Px].
		.

	note eq_such_intro: such_eq_intro[THEN eq.sym].

end

