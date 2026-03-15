---
# Zermelo-Fraenkel Set Theory

We formalize intuitionistic ZF set theory in a conservative axiomatic form.
There, operations to derive sets from others are not explicit, but
only the existence of the resulting sets is axiomatized.
---
import Sets.
---
Standard formulations of ZF "define" pairs using unordered pairs,
but formalizing the unique choice axiom schema already requires syntactic pairing.
Moreover, to justify notation `upair (x,y)`, the pair argument must belong to a class.
(Notation `upair x y` would even require Currying.)
So we just assume syntactic pairs of sets are sets.
---
assume pair_set: ∀x ∈ Set. ∀y ∈ Set. (x,y) ∈ Set.
note! pair_set[rule].


---
The unordered pair `{x,x}` gives the singleton `{x}`.
---

obtain singleton where
	singleton_Set! if x ∈ Set then {x} ∈ Set,
	singleton_iff: if x ∈ Set, y ∈ Set then y ∈ {x} ⟺ x = y;
	- for thesis if assm;
		apply abbrev_cond[of (x. x ∈ Set) (x. upair(x,x)) (x. Set)];
		- .
		- for f if f;
			apply assm[of f, unfold f];
			- .
			- if ! x ∈ Set, ! y ∈ Set then y ∈ upair(x,x) ⟺ x = y;
				unfold upair_iff or.idem;
				by iff_eq.commute.
			.
		.
	.

---
### Power Set
---
theory PowerSetAxiom:
	assume Pow_axiom: ∀x ∈ Set. ∃y ∈ Set. ∀z ∈ Set. z ∈ y ⟺ (∀w ∈ Set. w ∈ z ⟹ w ∈ x).
begin

	lemma Pow_ex1: if x! x ∈ Set then ∃!y ∈ Set. ∀z ∈ Set. z ∈ y ⟺ (∀w ∈ Set. w ∈ z ⟹ w ∈ x);
		apply Pow_axiom[rule, OF x, THEN in.ex_elim];
		- for X if X!, Xspec;
			apply in.ex1_intro1[of X];
			apply Xspec;
			apply X;
			- for X' if X'!, X'spec;
				by set_eq_intro #simp Xspec[rule] X'spec[rule].
			.
		.

	obtain Pow where
		Pow_Set! if x ∈ Set then Pow x ∈ Set,
		Pow_iff: if x ∈ Set, y ∈ Set then y ∈ Pow x ⟺ (∀z ∈ Set. z ∈ y ⟹ z ∈ x);
		- for thesis if assm;
			apply unique_choice_cond[of
					(x. x ∈ Set)
					(x. Set)
					((x,y). ∀z ∈ Set. z ∈ y ⟺ (∀w ∈ Set. w ∈ z ⟹ w ∈ x)),
				THEN ex_elim];
			simp;
			- by Pow_ex1.
			- for f if f;
				apply assm[of f];
				- if x: x ∈ Set;
					use f[OF x].
				- if x: x ∈ Set, y: y ∈ Set;
					use f[OF x]; by y.
				.
			.
		.
end

---
### Unions
---
theory BigCupAxiom:
	assume CUP_axiom: ∀x ∈ Set. ∃y ∈ Set. ∀z ∈ Set. z ∈ y ⟺ (∃w ∈ Set. w ∈ x ∧ z ∈ w).
begin

	lemma CUP_ex1: if x! x ∈ Set then ∃!y ∈ Set. ∀z ∈ Set. z ∈ y ⟺ (∃w ∈ Set. w ∈ x ∧ z ∈ w);
		apply CUP_axiom[rule, OF x, THEN in.ex_elim];
		- for y if y!, yspec;
			apply in.ex1_intro1[of y];
			- apply yspec.
			- apply y.
			- for y' if y'!, y'spec;
				apply set_eq_intro;
				by #simp yspec[rule] y'spec[rule].
			.
		.

	obtain (⋃) where
		CUP_Set! if x ∈ Set then ⋃x ∈ Set,
		CUP_iff: if x ∈ Set, y ∈ Set then y ∈ ⋃x ⟺ (∃z ∈ Set. z ∈ x ∧ y ∈ z);
		- for thesis if assm;
			apply unique_choice_cond[of
					(x. x ∈ Set)
					(x. Set)
					((x,y). ∀z ∈ Set. z ∈ y ⟺ (∃w ∈ Set. w ∈ x ∧ z ∈ w)),
				simp, OF CUP_ex1, THEN ex_elim];
			- for f if f;
				apply assm[of f];
				- for x if x;
					use f[OF x].
				- for x if x;
					use f[OF x].
				.
			.
		.

	obtain (∪) where
		cup_Set! if x ∈ Set, y ∈ Set then x ∪ y ∈ Set,
		cup_iff: if x ∈ Set, y ∈ Set, z ∈ Set then x ∈ y ∪ z ⟺ x ∈ y ∨ x ∈ z;
		- for thesis if assm;
			apply abbrev_cond[of (p. ∃x ∈ Set. ∃y ∈ Set. p = (x,y)) ((x,y). ⋃(upair(x,y))) (p. Set), simp];
			- by in.all_intro.
			- for (∪) if cup;
				apply assm[of (∪)];
				by #simp cup[OF _ _ eq.refl] CUP_iff upair_iff or_and_distrib in.ex_or_distrib in.ex_eq_and_iff.
			.
		.

end

---
### Infinity
---
assume infinity_axiom: ∃x ∈ Set. {} ∈ x ∧ (∀y ∈ x. y ∪ {y}).

---
### Foundation
---
assume foundation_axiom: ∀x ∈ Set. ¬ x = {} ⟹ ∃y ∈ Set. x ∈ y ∧ (∀z ∈ Set. z ∈ x ⟹ ¬ z ∈ y).

begin