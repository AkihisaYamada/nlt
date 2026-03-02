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
	by extensionality_axiom[rule, OF A B eq].

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
	apply upair_axiom[rule, OF x y, THEN in.ex_elim];
	- for z if z! z ∈ Set, zall;
		apply in.ex1_intro1[of z];
		- by in.all_intro zall.
		- by z.
		- apply in.all_intro;
			- for z' if !, z'all;
				apply set_eq_intro;
				- for w if w!;
					unfold z'all[rule] zall[rule].
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
	upair_Set! if x ∈ Set, y ∈ Set then upair x y ∈ Set,
	upair_iff: if x ∈ Set, y ∈ Set, z ∈ Set then z ∈ upair x y ⟺ z = x ∨ z = y;
- for thesis if assm;
	apply unique_choice2_cond[of ((x,y). x ∈ Set ∧ y ∈ Set) ((x,y,z). ∀w ∈ Set. w ∈ z ⟺ w = x ∨ w = y) Set, simp, THEN ex_elim];
	- by ex1_upair.
	- for f if f;
		apply assm[of f];
		- if x: x ∈ Set, y: y ∈ Set; use f[OF x y].
		- if x: x ∈ Set, y: y ∈ Set; use f[OF x y].
		.
	.
.

---
## Singleton
---

---
The unordered pair `{x,x}` gives the singleton `{x}`.
---
obtain _singleton where
	singleton_Set! if x ∈ Set then {x} ∈ Set,
	singleton_iff: if x ∈ Set, y ∈ Set then y ∈ {x} ⟺ x = y;
- for thesis if assm;
	apply abbrev_cond[of (x. x ∈ Set) (x. upair x x) Set, THEN ex_elim];
	- by in.all_intro.
	- for f if f;
		apply assm[of f, unfold f];
		- .
		- if ! x ∈ Set, ! y ∈ Set then y ∈ upair x x ⟺ x = y;
			unfold upair_iff or.idem;
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
note! pair_set[rule].

---
### Power Set
---
assume Pow_axiom: ∀x ∈ Set. ∃y ∈ Set. ∀z ∈ Set. z ∈ y ⟺ (∀w ∈ Set. w ∈ z ⟹ w ∈ x).

lemma Pow_ex1: if x! x ∈ Set then ∃!y ∈ Set. ∀z ∈ Set. z ∈ y ⟺ (∀w ∈ Set. w ∈ z ⟹ w ∈ x);
	apply Pow_axiom[rule, OF x, THEN in.ex_elim];
	- for X if X!, Xspec;
		apply in.ex1_intro1[of X];
		apply Xspec;
		apply X;
		apply in.all_intro;
		- for X' if X'!, X'spec;
			by set_eq_intro #simp Xspec[rule] X'spec[rule].
		.
	.

obtain Pow where
	Pow_Set! if x ∈ Set then Pow x ∈ Set,
	Pow_iff: if x ∈ Set, y ∈ Set then y ∈ Pow x ⟺ (∀z ∈ Set. z ∈ y ⟹ z ∈ x);
- for thesis if assm;
	apply unique_choice_cond[of (x. x ∈ Set) ((x,y). ∀z ∈ Set. z ∈ y ⟺ (∀w ∈ Set. w ∈ z ⟹ w ∈ x)) Set, THEN ex_elim];
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

---
### Unions
---
assume CUP_axiom: ∀x ∈ Set. ∃y ∈ Set. ∀z ∈ Set. z ∈ y ⟺ (∃w ∈ Set. w ∈ x ∧ z ∈ w).

lemma CUP_ex1: if x! x ∈ Set then ∃!y ∈ Set. ∀z ∈ Set. z ∈ y ⟺ (∃w ∈ Set. w ∈ x ∧ z ∈ w);
	apply CUP_axiom[rule, OF x, THEN in.ex_elim];
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
	CUP_Set! if x ∈ Set then ⋃x ∈ Set,
	CUP_iff: if x ∈ Set, y ∈ Set then y ∈ ⋃x ⟺ (∃z ∈ Set. z ∈ x ∧ y ∈ z);
	- for thesis if assm;
		apply unique_choice_cond[of (x. x ∈ Set) ((x,y). ∀z ∈ Set. z ∈ y ⟺ (∃w ∈ Set. w ∈ x ∧ z ∈ w)), simp, OF CUP_ex1, THEN ex_elim];
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
		apply abbrev2_cond[of ((x,y). x ∈ Set ∧ y ∈ Set) ((x,y). ⋃(upair x y)) Set, simp, THEN ex_elim];
		- by in.all_intro.
		- for (∪) if cup_def;
			apply assm[of (∪), simp cup_def];
			by #simp CUP_iff upair_iff or_and_distrib in.ex_or_distrib in.ex_eq_and_iff.
		.
	.

---
### Infinity
---
assume infinity_axiom: ∃x ∈ Set. {} ∈ x ∧ (∀y ∈ x. y ∪ {y}).

---
### Replacement

The axiom schema of replacement would be:
`∀P. ∀A ∈ Set. (∀x ∈ A. ∃!y ∈ Set. P.[x,y]) ⟹ ∃B ∈ Set. ∀y ∈ Set. y ∈ B ⟺ (∃x ∈ A. P.[x,y])`
but this formulation would not allow obtaining notation for given P via unique choice:
`∀P. ∀A ∈ Set. ∀x ∈ A. ∃!y ∈ Set. P.[x,y] ⟹ ∀y ∈ Set. y ∈ Replace A P ⟺ (∃x ∈ A. P.[x,y])`
This `P` have to be made into functional form:
---
assume replacement_schema: ∀P.
	∀A ∈ Set. (∀x ∈ A. ∃!y ∈ Set. P x y) ⟹ ∃B ∈ Set. ∀y ∈ Set. y ∈ B ⟺ (∃x ∈ A. P x y).

lemma replacement_ex1: for P A
	if A! A ∈ Set, ex1: ∀x ∈ A. ∃!y ∈ Set. P x y
	then ∃!B ∈ Set. ∀y ∈ Set. y ∈ B ⟺ (∃x ∈ A. P x y);
-	apply replacement_schema[THEN in.all_elim1, OF A ex1, THEN in.ex_elim];
	- for B if ! B ∈ Set, inB: ∀y ∈ Set. y ∈ B ⟺ (∃x ∈ A. P x y);
		apply+ in.ex1_intro1[of B] in.all_intro;
		- for y if ! y ∈ Set then y ∈ B ⟺ (∃x ∈ A. P x y);
			by inB[THEN in.all_elim1].
		- for B' if ! B' ∈ Set, inB': ∀y ∈ Set. y ∈ B' ⟺ (∃x ∈ A. P x y) then B' = B;
			by set_eq_intro #simp inB[rule] inB'[rule].
		.
	.
.

obtain Replace where
	Replace_Set: for P if A ∈ Set, ∀x ∈ A. ∃!y ∈ Set. P x y then Replace P A ∈ Set,
	Replace_iff: for P if A ∈ Set, ∀x ∈ A. ∃!y ∈ Set. P x y then ∀y ∈ Set. y ∈ Replace P A ⟺ (∃x ∈ A. P x y);
- for thesis if assm;
	apply unique_choice2_cond[of ((P,A). A ∈ Set ∧ (∀x ∈ A. ∃!y ∈ Set. P x y)) ((P,A,B). ∀y ∈ Set. y ∈ B ⟺ (∃x ∈ A. P x y)) Set, simp, THEN ex_elim];
	- for P A if A, ex1;
		by replacement_ex1[OF A ex1].
	- for f if f;
		apply assm[of f];
		- for P A if A, ex1;
			use f[OF A ex1].
		- for P A if A, ex1;
			use f[OF A ex1].
		.
	.
.

---
### Separation Schema

The separation schema assumes for any set and any predicate,
the existence of the subset of the former whose elements satisfy the latter.
---
assume separation_schema:
	∀P. ∀A ∈ Set. ∃B ∈ Set. ∀x ∈ Set. x ∈ B ⟺ x ∈ A ∧ P.[x].

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