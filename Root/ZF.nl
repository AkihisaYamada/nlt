---
# Zermelo-Fraenkel Set Theory

We formalize intuitionistic ZF set theory in a conservative axiomatic form.
There, operations to derive sets from others are not explicit, but
only the existence of the resulting sets is axiomatized.

We base on the first order logic defined via abbreviation.
---
import Abbreviation.
import FirstOrder.

---
`Set` is the (sole) quantifiable and equational type.
---
fix Set.

assume Set_EQTYPE! Set ∈ EQTYPE. -- One can equate sets.

---
Membership between sets is a proposition.
---
assume in_Prop! if x ∈ Set, A ∈ Set then (x ∈ A) ∈ Prop.

---
### Extensionality
---
assume extensionality_axiom: ∀A ∈ Set. ∀B ∈ Set. (∀x ∈ Set. x ∈ A ⟺ x ∈ B) ⟹ A = B.

---
As an inference rule:
---
lemma set_eq_intro: if eq: ∀x. x ∈ Set ⟹ x ∈ A ⟺ x ∈ B, A! A ∈ Set, B! B ∈ Set then A = B;
	apply extensionality_axiom[THEN allIn_elim1, OF A, THEN allIn_elim1, OF B];
	by allIn_intro eq.

---
### Empty set

The empty set is specified by an existential axiom (of type `Prop`):
---
assume ex_empty: ∃x ∈ Set. ¬(∃y ∈ Set. y ∈ x).

syntax {} := Empty.
obtain Empty where Empty_Set! {} ∈ Set, nex_in_empty: ¬(∃x ∈ Set. x ∈ {});
	- for thesis if assm;
		apply exIn_elim[OF ex_empty];
		- for e;
			by assm[of e].
		.
	.

---
### Unordered pairs

We need to admit more assumptions for more constructions;
for instance, the unordered pair $\{x,y\}$ is axiomatized by
---
assume upair_axiom: ∀x ∈ Set. ∀y ∈ Set. ∃z ∈ Set. ∀w ∈ Set. w ∈ z ⟺ w = x ∨ w = y.
---
Informally, then one assumes granted a binary operator which,
given `x` and `y` as arguments, denotes the (unique) `z`.
For given `x` and `y`, we can use `THE` operator to denote the `z`:
---
import TheIn.
---
---
note! ex1In_type TheIn_in.
print.
lemma ex1_upair: if x! x ∈ Set, y! y ∈ Set then ∃!z ∈ Set. ∀w ∈ Set. w ∈ z ⟺ w = x ∨ w = y;
	apply upair_axiom[unfolded+ allIn_iff, OF x y, THEN exIn_elim];
	- for z if z! z ∈ Set, zall;
		apply ex1In_intro1[of z];
		-; by zall.
		-; by z.
		-; apply allIn_intro;
			- for z' if !, z'all;
				apply set_eq_intro;
				- for w if w!;
					unfold z'all[unfolded allIn_iff] zall.
				.
			.
		.
	.
---
Since we have admitted abbreviations and `THE` operator, we can obtain the function for unordered pair.
---
obtain upair where
	upair_Set! if x ∈ Set, y ∈ Set then upair x y ∈ Set,
	upair_iff: if x ∈ Set, y ∈ Set, z ∈ Set then z ∈ upair x y ⟺ z = x ∨ z = y;
	- for thesis if assm;
		apply abbrev2[of (p. THE u ∈ Set. ∀z ∈ Set. z ∈ u ⟺ z = fst p ∨ z = snd p)];
		- for f if f;
			apply assm[of f];
			-; by f(simp) TheIn_in ex1_upair.
			- if ! x ∈ Set, ! y ∈ Set, ! z ∈ Set;
				note 1: TheIn_intro[of Set (u. ∀ z ∈ Set. z ∈ u ⟺ z = fst (x , y) ∨ z = snd (x , y)), simplified, folded f].
				apply 1[THEN allIn_elim1];
				apply ex1_upair.
			.
		.
	.
---
The unordered pair `{x,x}` gives the singleton `{x}`.
---
syntax {_} := singleton.
obtain singleton where
	singleton_Set! if x ∈ Set then {x} ∈ Set,
	singleton_iff: if x ∈ Set, y ∈ Set then y ∈ {x} ⟺ x = y;
	- for thesis if assm;
		apply abbrev[of (x. upair x x)];
		- for f if f;
			apply assm[of f, unfolded f];
			-; .
			- if ! x ∈ Set, ! y ∈ Set then y ∈ upair x x ⟺ x = y;
				unfold upair_iff iff.or.idem;
				by iff.eq.commute.
			.
		.
	.
---
### Power Set
---
assume Pow_axiom: ∀x ∈ Set. ∃y ∈ Set. ∀z ∈ Set. z ∈ y ⟺ (∀w ∈ Set. w ∈ z ⟹ w ∈ x).

lemma Pow_ex1: if x! x ∈ Set then ∃!y ∈ Set. ∀z ∈ Set. z ∈ y ⟺ (∀w ∈ Set. w ∈ z ⟹ w ∈ x);
	apply Pow_axiom[THEN allIn_elim1, OF x, THEN exIn_elim];
	- for X if X!, Xspec;
		apply ex1In_intro1[of X];
		apply Xspec;
		apply X;
		apply allIn_intro;
		- for X' if X'!, X'spec;
			by set_eq_intro #unfold Xspec[THEN allIn_elim1] X'spec[THEN allIn_elim1].
		.
	.

obtain Pow where
	Pow_Set! if x ∈ Set then Pow x ∈ Set,
	Pow_iff: if x ∈ Set, y ∈ Set then y ∈ Pow x ⟺ (∀z ∈ Set. z ∈ y ⟹ z ∈ x);
	- for thesis if assm;
		apply abbrev[of (x. THE X ∈ Set. ∀y ∈ Set. y ∈ X ⟺ (∀z ∈ Set. z ∈ y ⟹ z ∈ x))];
		- for f if f;
			apply assm[of f];
			by Pow_ex1[THEN TheIn_in, folded f] Pow_ex1[THEN TheIn_intro, folded f, THEN allIn_elim1].
		.
	.

---
### Unions
---
assume UN_axiom: ∀x ∈ Set. ∃y ∈ Set. ∀z ∈ Set. z ∈ y ⟺ (∃w ∈ Set. w ∈ x ∧ z ∈ w).

lemma UN_ex1: if x! x ∈ Set then ∃!y ∈ Set. ∀z ∈ Set. z ∈ y ⟺ (∃w ∈ Set. w ∈ x ∧ z ∈ w);
	apply UN_axiom[THEN allIn_elim1, OF x, THEN exIn_elim];
	- for y if y!, yspec;
		apply ex1In_intro1[of y];
		-; apply yspec.
		-; apply y.
		apply allIn_intro;
		- for y' if y'!, y'spec;
			apply set_eq_intro;
			- for z if z!;
				unfold yspec[THEN allIn_elim1] y'spec[THEN allIn_elim1].
			.
		.
	.

obtain (⋃) where
	UN_Set! if x ∈ Set then ⋃x ∈ Set,
	UN_iff: if x ∈ Set, y ∈ Set then y ∈ ⋃x ⟺ (∃z ∈ Set. z ∈ x ∧ y ∈ z);
	- for thesis if assm;
		apply abbrev[of (x. THE U ∈ Set. ∀y ∈ Set. y ∈ U ⟺ (∃z ∈ Set. z ∈ x ∧ y ∈ z))];
		- for f if f;
			apply assm[of f];
			by UN_ex1[THEN TheIn_in, folded f] UN_ex1[THEN TheIn_intro, folded f, THEN allIn_elim1].
		.
	.

obtain (∪) where
	cup_Set! if x ∈ Set, y ∈ Set then x ∪ y ∈ Set,
	cup_iff: if x ∈ Set, y ∈ Set, z ∈ Set then x ∈ y ∪ z ⟺ x ∈ y ∨ x ∈ z;
	- for thesis if assm;
		apply abbrev2[of (p. ⋃(upair (fst p) (snd p)))];
		- for (∪) if cup_def;
			apply assm[of (∪), simplified cup_def];
			-; .
			- if x! x ∈ Set, y! y ∈ Set, z! z ∈ Set then x ∈ ⋃(upair y z) ⟺ x ∈ y ∨ x ∈ z;
				unfold UN_iff upair_iff;
				apply iff_intro;
				- if un;
					apply un[THEN exIn_elim, simplified and_imp_iff_imp_imp];
					- if w! w ∈ Set, or: w = y ∨ w = z, xw: x ∈ w then x ∈ y ∨ x ∈ z;
						apply or_elim[OF or];
						- if wy;
							by or_iff_true1(simp) xw[unfolded wy].
						- if wz;
							by or_iff_true2(simp) xw[unfolded wz].
						.
					.
				- if or;
					apply or_elim[OF or];
					-; by exIn_intro1[of y].
					-; by exIn_intro1[of z].
					.
				.
			.
		.
	.

---
### Infinity
---
assume infinity_axiom: ∃x ∈ Set. {} ∈ x ∧ (∀y ∈ x. y ∪ {y}).

---
### Separation Schema

The separation schema assumes for any set and any predicate,
the existence of the subset of the former whose elements satisfy the latter.
---
assume separation_schema:
	if p ∈ Set → Prop
	then ∀x ∈ Set. ∃y ∈ Set. ∀z ∈ Set. z ∈ y ⟺ z ∈ x ∧ p z.

lemma separation_ex1:
	if p: p ∈ Set → Prop, x: x ∈ Set
	then ∃!y ∈ Set. ∀z ∈ Set. z ∈ y ⟺ z ∈ x ∧ p z;
	apply separation_schema[OF p, THEN allIn_elim1, OF x, THEN exIn_elim];
	- for y if y, yspec;
		apply+ ex1In_intro1[of y] allIn_intro y;
		-; by yspec[THEN allIn_elim1](simp).
		- for y' if y', y'spec;
			by set_eq_intro y y' #unfold yspec[THEN allIn_elim1] y'spec[THEN allIn_elim1].
		.
	.

obtain separation where
	separation_Set! if p ∈ Set → Prop, x ∈ Set then separation x p ∈ Set,
	separation_iff: if p ∈ Set → Prop, x ∈ Set, z ∈ Set then z ∈ separation x p ⟺ z ∈ x ∧ p z;
	- for thesis if assm;
		apply abbrev2[of (p. THE y ∈ Set. ∀z ∈ Set. z ∈ y ⟺ z ∈ fst p ∧ snd p z)];
		- for f if f;
			apply assm[of f, folded+ and_imp_iff_imp_imp all_and_distrib imp_and_distrib];
			- if p: p ∈ Set → Prop, x: x ∈ Set;
				have 1: ∃!y ∈ Set. ∀z ∈ Set. z ∈ y ⟺ z ∈ fst (x,p) ∧ snd (x,p) z;
					by separation_ex1[OF p x].
				by TheIn_in[OF 1, folded f] TheIn_intro[OF 1, folded f, simplified, THEN allIn_elim1].
			.
		.
	.

---
### Replacement
---
assume replacement_schema:
	if P ∈ Set → Set → Prop
	then (∀x ∈ Set. ∃!y ∈ Set. P x y) ⟹ ∀w ∈ Set. ∃v ∈ Set. ∀r ∈ Set. r ∈ v ⟺ (∃s ∈ Set. s ∈ w ∧ P s r).

lemma replacement_ex1:
	if P! P ∈ Set → Set → Prop, ex1: ∀x ∈ Set. ∃!y ∈ Set. P x y, w! w ∈ Set
	then ∃!v ∈ Set. ∀r ∈ Set. r ∈ v ⟺ (∃s ∈ Set. s ∈ w ∧ P s r);
-- proof
	apply replacement_schema[OF P ex1, THEN allIn_elim1, OF w, THEN exIn_elim];
	note! P[THEN fun_elim1, THEN fun_elim1].
	- for v if v! v ∈ Set, in_v: ∀ r ∈ Set. r ∈ v ⟺ (∃ s ∈ Set. s ∈ w ∧ P s r);
		apply+ ex1In_intro1[of v] allIn_intro;
		- for x if x! x ∈ Set then x ∈ v ⟺ (∃ s ∈ Set. s ∈ w ∧ P s x);
			by in_v[THEN allIn_elim1].
		- for x if x! x ∈ Set, in_x: ∀ r ∈ Set. r ∈ x ⟺ (∃ s ∈ Set. s ∈ w ∧ P s r) then x = v;
			by set_eq_intro #unfold in_v[THEN allIn_elim1] in_x[THEN allIn_elim1].
		.
	.
-- qed

obtain Replace where
	Replace_Set! if P ∈ Set → Set → Prop, ∀x ∈ Set. ∃!y ∈ Set. P x y, w ∈ Set then Replace P w ∈ Set,
	Replace_iff: if P ∈ Set → Set → Prop, ∀x ∈ Set. ∃!y ∈ Set. P x y, w ∈ Set, r ∈ Set
		then r ∈ Replace P w ⟺ (∃s ∈ Set. s ∈ w ∧ P s r);
	- for thesis if assm;
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
### Foundation
---
assume foundation_axiom: ∀x ∈ Set. x ≠ {} ⟹ ∃y ∈ Set. x ∈ y ∧ (∀z ∈ Set. z ∈ x ⟹ z ∉ y).

begin