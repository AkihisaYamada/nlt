---
# Zermelo-Fraenkel Set Theory

We formalize intuitionistic ZF set theory in a conservative axiomatic form.
There, operations to derive sets from others are not explicit, but
only the existence of the resulting sets is axiomatized.

We base on the minimal first order equational logic, where
`Set` is the (sole) quantifiable and equational type.
---
print.
import Eq.
import TypeFree.
import Minimal.
import AllEx1In.
fix Set.

---
### Extensionality
---
assume extensionality_axiom: ∀A ∈ Set. ∀B ∈ Set. (∀x ∈ Set. x ∈ A ⟺ x ∈ B) ⟹ A = B.

---
As an inference rule:
---
lemma set_eq_intro: if eq: ∀x. x ∈ Set ⟹ x ∈ A ⟺ x ∈ B, A! A ∈ Set, B! B ∈ Set then A = B;
	apply extensionality_axiom[THEN in.all_elim1, OF A, THEN in.all_elim1, OF B];
	by in.all_intro eq.

---
### Empty set

The empty set is specified by an existential axiom (of type `Prop`):
---
assume ex_empty: ∃x ∈ Set. ¬(∃y ∈ Set. y ∈ x).

obtain _empty where empty_Set! {} ∈ Set, nex_in_empty: ¬(∃x ∈ Set. x ∈ {});
	- for thesis if assm;
		apply in.ex_elim[OF ex_empty];
		- for e;
			by assm[of e].
		.
	.

---
### Unordered pairs

The unordered pair $\{x,y\}$ is axiomatized by:
---
assume upair_axiom: ∀x ∈ Set. ∀y ∈ Set. ∃z ∈ Set. ∀w ∈ Set. w ∈ z ⟺ w = x ∨ w = y.
---
One can prove such `z` is unique:
---
lemma ex1_upair: if x! x ∈ Set, y! y ∈ Set then ∃!z ∈ Set. ∀w ∈ Set. w ∈ z ⟺ w = x ∨ w = y;
	apply upair_axiom[unfold+ in.all_def, OF x y, THEN in.ex_elim];
	- for z if z! z ∈ Set, zall;
		apply in.ex1_intro1[of z];
		- by in.all_intro zall.
		- by z.
		- apply in.all_intro;
			- for z' if !, z'all;
				apply set_eq_intro;
				- for w if w!;
					unfold z'all[unfold in.all_def] zall.
				.
			.
		.
	.
---
Usual formulations of ZF then introduces a binary operator which,
given `x` and `y` as arguments, denotes the (unique) such `z`.
In Naive Logic, this assumption must be explicitly formalized.
We do so by a binary unique choice axiom schema.
---
import UniqueChoice2.

obtain upair where
	upair_spec: if x ∈ Set, y ∈ Set then upair x y ∈ Set ∧ (∀z ∈ Set. z ∈ upair x y ⟺ z = x ∨ z = y);
- for thesis if assm;
	apply unique_choice2_cond[of ((x,y). x ∈ Set ∧ y ∈ Set) ((x,y,z). ∀w ∈ Set. w ∈ z ⟺ w = x ∨ w = y) Set, simp, THEN ex_elim];
	- by ex1_upair.
	- for f if f;
		apply assm[of f];
		by f.
	.
.

lemma upair_Set! if x: x ∈ Set, y: y ∈ Set then upair x y ∈ Set;
	use upair_spec[OF x y].

lemma in_upair: if x: x ∈ Set, y: y ∈ Set, z: z ∈ Set then z ∈ upair x y ⟺ z = x ∨ z = y;
	use upair_spec[OF x y];
	simp in.all_def;
	- if 1, 2;
		by 2[OF z].
	.

---
## Singleton
---

---
The unordered pair `{x,x}` gives the singleton `{x}`.
---
obtain _singleton where
	singleton_Set! if x ∈ Set then {x} ∈ Set,
	in_singleton: if x ∈ Set, y ∈ Set then y ∈ {x} ⟺ x = y;
- for thesis if assm;
	apply abbrev_cond[of (x. x ∈ Set) (x. upair x x) Set, THEN ex_elim];
	- by in.all_intro.
	- for f if f;
		apply assm[of f, unfold f];
		- .
		- if ! x ∈ Set, ! y ∈ Set then y ∈ upair x x ⟺ x = y;
			unfold in_upair or.idem;
			by iff_eq.commute.
		.
	.
.
---
Standard formulations of ZF "define" pairs using unordered pairs,
but formalizing the unique choice axiom schema already requires syntactic pairing.
So we just assume syntactic pairs of sets are sets.
---
assume pair_set: ∀x ∈ Set. ∀y ∈ Set. (x,y) ∈ Set.
print.
note! pair_set[rule].

---
### Power Set
---
assume Pow_axiom: ∀x ∈ Set. ∃y ∈ Set. ∀z ∈ Set. z ∈ y ⟺ (∀w ∈ Set. w ∈ z ⟹ w ∈ x).

lemma Pow_ex1: if x! x ∈ Set then ∃!y ∈ Set. ∀z ∈ Set. z ∈ y ⟺ (∀w ∈ Set. w ∈ z ⟹ w ∈ x);
	apply Pow_axiom[THEN in.all_elim1, OF x, THEN in.ex_elim];
	- for X if X!, Xspec;
		apply in.ex1_intro1[of X];
		apply Xspec;
		apply X;
		apply in.all_intro;
		- for X' if X'!, X'spec;
			by set_eq_intro #simp Xspec[THEN in.all_elim1] X'spec[THEN in.all_elim1].
		.
	.

obtain Pow where
	Pow_Set! if x ∈ Set then Pow x ∈ Set,
	in_Pow: if x ∈ Set, y ∈ Set then y ∈ Pow x ⟺ (∀z ∈ Set. z ∈ y ⟹ z ∈ x);
- for thesis if assm;
	apply unique_choice_cond[of (x. x ∈ Set) ((x,y). ∀z ∈ Set. z ∈ y ⟺ (∀w ∈ Set. w ∈ z ⟹ w ∈ x)) Set, THEN ex_elim];
	simp;
	- by in.all_intro Pow_ex1.
	- for f if f;
		apply assm[of f];
		- if x: x ∈ Set;
			use f[OF x].
		- if x: x ∈ Set, y: y ∈ Set;
			use f[OF x]; simp; .
	.
.

note Pow_Set! Pow_type[THEN fun_elim1].

---
### Unions
---
assume UN_axiom: ∀x ∈ Set. ∃y ∈ Set. ∀z ∈ Set. z ∈ y ⟺ (∃w ∈ Set. w ∈ x ∧ z ∈ w).

lemma UN_ex1: if x! x ∈ Set then ∃!y ∈ Set. ∀z ∈ Set. z ∈ y ⟺ (∃w ∈ Set. w ∈ x ∧ z ∈ w);
	apply UN_axiom[THEN in.all_elim1, OF x, THEN in.ex_elim];
	- for y if y!, yspec;
		apply in.ex1_intro1[of y];
		- apply yspec.
		- apply y.
		apply in.all_intro;
		- for y' if y'!, y'spec;
			apply set_eq_intro;
			- for z if z!;
				unfold yspec[THEN in.all_elim1] y'spec[THEN in.all_elim1].
			.
		.
	.

obtain (⋃) where
	UN_type: (⋃) ∈ Set → Set,
	UN_iff: if x ∈ Set, y ∈ Set then y ∈ ⋃x ⟺ (∃z ∈ Set. z ∈ x ∧ y ∈ z);
	- for thesis if assm;
		apply unique_choice_set[of ((x,y). ∀z ∈ Set. z ∈ y ⟺ (∃w ∈ Set. w ∈ x ∧ z ∈ w)), THEN in.ex_elim];
		simp;
		- by in.all_intro UN_ex1.
		- for f if ty, f;
			apply assm[OF ty];
			unfold f[THEN in.all_elim1, THEN in.all_elim1].
		.
	.

note UN_Set! UN_type[THEN fun_elim1].

obtain (∪) where
	cup_type: (∪) ∈ Set → Set → Set,
	cup_iff: if x ∈ Set, y ∈ Set, z ∈ Set then x ∈ y ∪ z ⟺ x ∈ y ∨ x ∈ z;
	- for thesis if assm;
		apply abbrev2_set[of ((x,y). ⋃(upair x y)), THEN in.ex_elim];
		simp;
		- by in.all_intro.
		- for (∪) if cup_type, cup_def;
			apply assm[OF cup_type, simp cup_def[THEN in.all_elim1, THEN in.all_elim1]];
			- if x! x ∈ Set, y! y ∈ Set, z! z ∈ Set then x ∈ ⋃(upair y z) ⟺ x ∈ y ∨ x ∈ z;
				unfold UN_iff upair_iff;
				simp or_and_distrib in.ex_or_distrib in.ex_eq_and_iff iff_true[OF x] iff_true[OF y] iff_true[OF z].
			.
		.
	.

---
### Infinity
---
assume infinity_axiom: ∃x ∈ Set. {} ∈ x ∧ (∀y ∈ x. y ∪ {y}).

---
### Replacement

The replacement schema would be:
```
	for P if A ∈ Set, ∀x ∈ A. ∃!y ∈ Set. P x y
	then ∃B ∈ Set. ∀y ∈ Set. y ∈ B ⟺ (∃x ∈ A. P x y).	
```
However, this cannot yield the notation `Replace P A` to denote the `B`.
The problem is that `P` is not a set but we only assumed unique choice on set arguments.

---
assume replacement_schema: ∀F. ∀A ∈ Set.
	(∀x ∈ A. ∃!y ∈ Set. F.[x,y]) ⟹ ∃B ∈ Set. ∀y ∈ Set. y ∈ B ⟺ (∃x ∈ A. F.[x,y]).	

lemma replacement_ex1:
	if F: F ∈ Set, ex1: ∀x ∈ Set. ∃!y ∈ Set. (x,y) ∈ F, w! w ∈ Set
	then ∃!v ∈ Set. ∀r ∈ Set. r ∈ v ⟺ (∃s ∈ Set. s ∈ w ∧ (s,r) ∈ F);
-	apply replacement_schema[OF ex1, THEN in.all_elim1, OF w, THEN in.ex_elim];
	- for v if v! v ∈ Set, in_v: ∀ r ∈ Set. r ∈ v ⟺ (∃ s ∈ Set. s ∈ w ∧ P s r);
		apply+ in.ex1_intro1[of v] in.all_intro;
		- for x if x! x ∈ Set then x ∈ v ⟺ (∃ s ∈ Set. s ∈ w ∧ P s x);
			by in_v[THEN in.all_elim1].
		- for x if x! x ∈ Set, in_x: ∀ r ∈ Set. r ∈ x ⟺ (∃ s ∈ Set. s ∈ w ∧ P s r) then x = v;
			by set_eq_intro #simp in_v[THEN in.all_elim1] in_x[THEN in.all_elim1].
		.
	.
.

obtain Replace where Replace_spec: if ∀x ∈ Set. ∃!y ∈ Set. P x y, w ∈ Set then
		Replace P w ∈ Set ∧ (∀r ∈ Set. r ∈ Replace P w ⟺ (∃s ∈ Set. s ∈ w ∧ P s r));
- for thesis if assm: ∀Replace.
	(∀P. (∀x ∈ Set. ∃!y ∈ Set. P x y) ⟹
		∀w. w ∈ Set ⟹ Replace P w ∈ Set ∧ (∀r ∈ Set. r ∈ Replace P w ⟺ (∃s ∈ Set. s ∈ w ∧ P s r))
	) ⟹ thesis;
	apply unique_choice2_set_rule[of ((P,w,v). ∀r ∈ Set. r ∈ v ⟺ (∃s ∈ Set. s ∈ w ∧ P s r)),simp];

	apply abbrev2[of (p. THE v ∈ Set. ∀r ∈ Set. r ∈ v ⟺ (∃s ∈ Set. s ∈ snd p ∧ fst p s r))];
	- for f if f;
		apply assm[of f, folded+ and_imp_iff_imp_imp all_and_distrib imp_and_distrib, unfolded and_imp_iff_imp_imp];
		- if P: P ∈ Set → Set → Prop, ex1: ∀x ∈ Set. ∃!y ∈ Set. P x y, w: w ∈ Set;
			have 1: ∃! v ∈ Set. ∀ r ∈ Set. r ∈ v ⟺ (∃ s ∈ Set. s ∈ snd (P,w) ∧ fst (P,w) s r);
				by replacement_ex1[OF P ex1 w].
			by TheIn_in[OF 1, folded f] TheIn_intro[OF 1, folded f, simplified, THEN allIn_elim1].
		.
	.
.

---
### Separation Schema

The separation schema assumes for any set and any predicate,
the existence of the subset of the former whose elements satisfy the latter.
---
assume separation_schema:
	for P then ∀A ∈ Set. ∃B ∈ Set. ∀x ∈ Set. x ∈ B ⟺ x ∈ A ∧ P.[x].

lemma separation_ex1:
	for P if A: A ∈ Set
	then ∃!B ∈ Set. ∀x ∈ Set. x ∈ B ⟺ x ∈ A ∧ P.[x];
	apply separation_schema[of P, THEN in.all_elim1, OF A, THEN in.ex_elim];
	- for B if B, Bspec;
		apply+ in.ex1_intro1[of B] in.all_intro B;
		- by yspec[THEN in.all_elim1](simp).
		- for B' if B', B'spec;
			by set_eq_intro B B' #unfold yspec[THEN in.all_elim1] B'spec[THEN in.all_elim1].
		.
	.

obtain separation where
	separation_type: for P then separation ∈ Set → Set → Set,
	separation_iff: if p ∈ Set → Prop, x ∈ Set, z ∈ Set then z ∈ separation x p ⟺ z ∈ x ∧ p z;
	- for thesis if assm;
		apply unique_choice2_set[of (t. ∀z ∈ Set. z ∈ snd (snd t) ⟺ z ∈ fst t ∧ fst (snd t) z), THEN in.ex_elim];
		simp;
		- apply separation_ex1
		- for f if ty, f;
			apply assm[of f, folded+ and_imp_iff_imp_imp all_and_distrib imp_and_distrib];
			- if p: p ∈ Set → Prop, x: x ∈ Set;
				have 1: ∃!y ∈ Set. ∀z ∈ Set. z ∈ y ⟺ z ∈ fst (x,p) ∧ snd (x,p) z;
					by separation_ex1[OF p x].
				by TheIn_in[OF 1, folded f] TheIn_intro[OF 1, folded f, simplified, THEN allIn_elim1].
			.
		.
	.

---
### Foundation
---
assume foundation_axiom: ∀x ∈ Set. x ≠ {} ⟹ ∃y ∈ Set. x ∈ y ∧ (∀z ∈ Set. z ∈ x ⟹ z ∉ y).

begin