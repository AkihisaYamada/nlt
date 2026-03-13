---
# Zermelo-Fraenkel Set Theory

We formalize intuitionistic ZF set theory in a conservative axiomatic form.
There, operations to derive sets from others are not explicit, but
only the existence of the resulting sets is axiomatized.

We base on the minimal first order equational logic, where
`Set` is the (sole) quantifiable and equational type.
---
print.
fix Set.
import Eq.
import TypeFree.
import Minimal.
import Membership.
import AllIn.
import ExIn.
import Ex1In.

---
## Axiomatization

### Extensionality

Extensionality asserts that sets `A` and `B` are equal if `x ∈ A ⟺ x ∈ B` for any `x`.
Strictly speaking, ZF variables range over sets, so this axiom would be formalized to
`∀A ∈ Set. ∀B ∈ Set. (∀x ∈ Set. x ∈ A ⟺ x ∈ B) ⟹ A = B`
but restricting `x` to `Set` here is useless.
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

syntax {} := empty.
obtain empty where empty_Set! {} ∈ Set, nex_in_empty: ¬(∃x ∈ Set. x ∈ {});
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
		- for z' if !, z'all;
			apply set_eq_intro;
			- for w if w!;
				unfold z'all[rule] zall[rule].
			.
		.
	.
---
Usual formulations of ZF then introduces a binary operator which,
given `x` and `y` as arguments, denotes the (unique) such `z`.
In Naive Logic, the assumption that one can do this must be explicitly formalized.
We do so by a unique choice axiom schema.
---
import UniqueChoiceCond.
---
Standard formulations of ZF "define" pairs using unordered pairs,
but formalizing the unique choice axiom schema already requires syntactic pairing.
Moreover, to justify notation `upair (x,y)`, the pair argument must belong to a class.
(Notation `upair x y` would even require Currying.)
So we just assume syntactic pairs of sets are sets.
---
assume pair_set: ∀x ∈ Set. ∀y ∈ Set. (x,y) ∈ Set.
note! pair_set[rule].

obtain upair where
	upair_Set! if x ∈ Set, y ∈ Set then upair(x,y) ∈ Set,
	upair_iff: if x ∈ Set, y ∈ Set, z ∈ Set then z ∈ upair(x,y) ⟺ z = x ∨ z = y;
	- for thesis if assm;
		apply unique_choice_cond[of (p. ∃x ∈ Set. ∃y ∈ Set. p = (x,y)) (p. Set) (((x,y),z). ∀w ∈ Set. w ∈ z ⟺ w = x ∨ w = y), simp, THEN ex_elim];
		- by ex1_upair.
		- for f if f;
			apply assm[of f];
			- if x: x ∈ Set, y: y ∈ Set; use f[OF x y eq.refl].
			- if x: x ∈ Set, y: y ∈ Set; use f[OF x y eq.refl].
			.
		.
	.

---
## Singleton
---

---
The unordered pair `{x,x}` gives the singleton `{x}`.
---
syntax {_} := singleton.
obtain singleton where
	singleton_Set! if x ∈ Set then {x} ∈ Set,
	singleton_iff: if x ∈ Set, y ∈ Set then y ∈ {x} ⟺ x = y;
	- for thesis if assm;
		apply abbrev_cond[of (x. x ∈ Set) (x. upair(x,x)) (x. Set)];
		- by in.all_intro.
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
assume Pow_axiom: ∀x ∈ Set. ∃y ∈ Set. ∀z ∈ Set. z ∈ y ⟺ (∀w ∈ Set. w ∈ z ⟹ w ∈ x).

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
		apply unique_choice_cond[of (x. x ∈ Set) (x. Set) ((x,y). ∀z ∈ Set. z ∈ y ⟺ (∀w ∈ Set. w ∈ z ⟹ w ∈ x)), THEN ex_elim];
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
		apply unique_choice_cond[of (x. x ∈ Set) (x. Set) ((x,y). ∀z ∈ Set. z ∈ y ⟺ (∃w ∈ Set. w ∈ x ∧ z ∈ w)), simp, OF CUP_ex1, THEN ex_elim];
		- for f if f;
			apply assm[of f];
			- for x if x;
				use f[OF x].
			- for x if x;
				use f[OF x].
			.
		.
	.

infix ∪(,) 71 70 71.

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

---
### Infinity
---
assume infinity_axiom: ∃x ∈ Set. {} ∈ x ∧ (∀y ∈ x. y ∪ {y}).

---
### Replacement

The axiom schema of replacement would be:
`∀P. ∀A ∈ Set. (∀x ∈ A. ∃!y ∈ Set. P.[x,y]) ⟹ ∃B ∈ Set. ∀y ∈ Set. y ∈ B ⟺ (∃x ∈ A. P.[x,y])`
but this formulation would not allow obtaining notation `Replace(A,P)` for this `B`,
because this `P` cannot be given as a tuple argument to the unique choice schema.
Instead, we assume the following variant:
---
assume image_ex: ∀f.
	∀A ∈ Set. (∀x ∈ A. f x ∈ Set) ⟹ ∃B ∈ Set. ∀y ∈ Set. y ∈ B ⟺ (∃x ∈ A. y = f x).
---
As we have already assumed unique choice, the standard axiom schema is derivable:
---
lemma replacement_schema:
	if A: A ∈ Set, ex1: ∀x ∈ A. ∃!y ∈ Set. P.[x,y]
	then ∃B ∈ Set. ∀y ∈ Set. y ∈ B ⟺ (∃x ∈ A. P.[x,y]);
	- apply unique_choice_cond[of (x. x ∈ A) (x. Set) P, THEN ex_elim];
		- by ex1[rule].
		- for f if f;
			have Pf: for x y if x: x ∈ A, y: y ∈ Set then P.[x,y] ⟺ y = f x;
				have fx: f x ∈ Set;
					use f[OF x].
				have Pfx: P.[x, f x];
					use f[OF x].
				unfold ex1[rule, OF x, THEN in.ex1_imp_iff_eq, OF fx Pfx y];
				by iff_eq.commute.
			apply image_ex[of f, rule, OF A, THEN in.ex_elim];
			- for x if x; use f[OF x].
			- for B if B, B_iff;
				apply in.ex_intro1[OF B];
				simp B_iff[rule] Pf.
			.
		.
	.

lemma image_ex1: for f
	if A! A ∈ Set, f: ∀x ∈ A. f x ∈ Set
	then ∃!B ∈ Set. ∀y ∈ Set. y ∈ B ⟺ (∃x ∈ A. y = f x);
	-	apply image_ex[rule, OF A f[rule], THEN in.ex_elim];
		- for B if B! B ∈ Set, inB: ∀y ∈ Set. y ∈ B ⟺ (∃x ∈ A. y = f x);
			apply+ in.ex1_intro1[of B] in.all_intro;
			- by inB[rule].
			-.
			- for B' if ! B' ∈ Set, inB': ∀y ∈ Set. y ∈ B' ⟺ (∃x ∈ A. y = f x) then B' = B;
				by set_eq_intro #simp inB[rule] inB'[rule].
			.
		.
	.

infix `(,) 101 100 100.
obtain (`) where
	image_Set: if A ∈ Set, ∀x ∈ A. f x ∈ Set then f ` A ∈ Set,
	image_iff: if A ∈ Set, ∀x ∈ A. f x ∈ Set, y ∈ Set then y ∈ f ` A ⟺ (∃x ∈ A. y = f x);
	- for thesis if assm;
		apply unique_choice_cond[
			of (p. ∃f. ∃A ∈ Set. p = (f,A) ∧ (∀x ∈ A. f x ∈ Set))
			   (p. Set)
			   (((f,A),B). ∀y ∈ Set. y ∈ B ⟺ (∃x ∈ A. y = f x)),
			simp, THEN ex_elim];
		- by image_ex1.
		- for (`) if im;
			apply assm[of (`)];
			- if A: A ∈ Set, f: ∀x ∈ A. f x ∈ Set;
				use im[OF A eq.refl f].
			- if A: A ∈ Set, f: ∀x ∈ A. f x ∈ Set;
				use im[OF A eq.refl f];.
			.
		.
	.

infix ∩(,) 81 80 81.
infix ×(,) 111 110 110.


---
### Separation Schema

The separation schema assumes for any set and any predicate,
the existence of the subset of the former whose elements satisfy the latter.
---
assume separation_schema: ∀P. ∀A ∈ Set. ∃B ∈ Set. ∀x ∈ Set. x ∈ B ⟺ x ∈ A ∧ P.[x].

lemma separation_ex1:
	for P if A: A ∈ Set
	then ∃!B ∈ Set. ∀x ∈ Set. x ∈ B ⟺ x ∈ A ∧ P.[x];
	apply separation_schema[of P, rule, OF A, THEN in.ex_elim];
	- for B if B, Bspec;
		apply+ in.ex1_intro1[of B] in.all_intro B;
		- by Bspec[rule](simp).
		- for B' if B', B'spec;
			by set_eq_intro B B' #simp Bspec[rule] B'spec[rule].
		.
	.

syntax {_ ∈ _. _} := CollectIn(,).
obtain CollectIn where
	CollectIn: for A P if A ∈ Set then {x ∈ A. P.[x]} ∈ Set,
	CollectIn_iff: for A P if A ∈ Set, x ∈ Set then x ∈ {x ∈ A. P.[x]} ⟺ x ∈ A ∧ P.[x];
	- for thesis if assm;
		apply unique_choice_cond[
			of (p. ∃A P. p = (A, x. P.[x]) ∧ A ∈ Set)
			   (p. Set)
			   (t. ∀A P B. t = ((A, x. P.[x]), B) ⟹ ∀x ∈ Set. x ∈ B ⟺ x ∈ A ∧ P.[x]),
			THEN ex_elim];
		simp;
		- for p A P if p, A;
			apply separation_ex1[OF A, THEN in.ex1_cong[THEN iff_elim1, OF eq.refl _ (1)], of (x. P.[x])];
			simp p;
			- for B if Bty;
				apply iff_intro;
				- if B for A' P' B' if A', P', B';
					fold A' unbind_cong[OF P'] B';
					by B.
				- if imp;
					apply imp;
					simp.
				.
			.
		- for CollectIn if c;
			apply assm[of CollectIn];
			- for A P if A;
				apply c[THEN and_elim1, of (A, x. P.[x]), simp, OF eq.refl eq.refl A].
			- for A P if A;
				use c[THEN and_elim2, of (A, x. P.[x]), simp, OF eq.refl eq.refl A eq.refl eq.refl eq.refl];.
			.
		.
	.

---
### Foundation
---
assume foundation_axiom: ∀x ∈ Set. ¬ x = {} ⟹ ∃y ∈ Set. x ∈ y ∧ (∀z ∈ Set. z ∈ x ⟹ ¬ z ∈ y).

begin