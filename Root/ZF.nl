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
`Set` is the (sole) quantifiable and equatable type.
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
lemma set_eq_intro: for A B if eq: ∀x. x ∈ Set ⟹ x ∈ A ⟺ x ∈ B, A! A ∈ Set, B! B ∈ Set then A = B;
	note 1: all.elim1[OF extensionality_axiom A ! !].
	apply all.elim1[OF 1 B ! !];
	by all.intro eq.

---
### Empty set

The empty set is specified by an existential axiom (of type `Prop`):
---
assume empty_axiom: ∃x ∈ Set. ¬(∃y ∈ Set. y ∈ x).

set compr {} := Empty.
obtain Empty where Empty_Set! {} ∈ Set, nex_in_empty: ¬(∃x ∈ Set. x ∈ {});
- for thesis if assm;
	apply ex.elim[OF empty_axiom];
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
import The.
---
---
note! ex1_type THE_type.

lemma upair_ex1:
	if x! x ∈ Set, y! y ∈ Set then ∃!z ∈ Set. ∀w ∈ Set. w ∈ z ⟺ w = x ∨ w = y;
apply upair_axiom[THEN all.elim1, OF x ! !, THEN all.elim1, OF y ! !, THEN ex.elim];
- for z if !, zall;
	apply ex1_intro[of z];
	apply zall;
	apply all.intro;
	- for z' if !, z'all;
		apply set_eq_intro;
		- for w if w!;
			unfold z'all[THEN all.elim1] zall[THEN all.elim1].
		.
	.
.
---
Since we have admitted abbreviations, we can denote the 
---
obtain upair where
	upair_Set! ∀x y. x ∈ Set ⟹ y ∈ Set ⟹ upair x y ∈ Set,
	upair_iff: ∀x y z. x ∈ Set ⟹ y ∈ Set ⟹ z ∈ Set ⟹ z ∈ upair x y ⟺ z = x ∨ z = y;
- for thesis if assm;
	apply assm[of (λx y. THE z ∈ Set. ∀w ∈ Set. w ∈ z ⟺ w = x ∨ w = y)];
	- for x y if !, !;
		unfold(=) beta.
	- for x y z if x!, y!, z!;
		unfold(=) beta;
		by ex1_imp_THE[OF upair_ex1[OF x y] ! !, THEN all.elim1, OF z ! !].
	by #unfold(=) beta.
by #unfold(=) beta.
---
The unordered pair `{x,x}` gives the singleton `{x}`.
---
obtain singleton where
	singleton_Set! ∀x. x ∈ Set ⟹ singleton x ∈ Set,
	singleton_iff: ∀x y. x ∈ Set ⟹ y ∈ Set ⟹ y ∈ singleton x ⟺ x = y;
- for thesis if assm;
	apply assm[of (λx. upair x x)];
	- for x if x!;
		unfold(=) beta.
	- for x y if x!, y!;
		unfold(=) beta;
		unfold upair_iff iff.or.idem;
		apply iff.intro;
		- if xy;
			by #unfold xy.
		- if yx;
			by #unfold yx.
		.
	.
.
---
### Power Set
---
assume Pow_axiom: ∀x ∈ Set. ∃y ∈ Set. ∀z ∈ Set. z ∈ y ⟺ (∀w ∈ Set. w ∈ z ⟹ w ∈ x).

lemma Pow_ex1: if x! x ∈ Set then ∃!y ∈ Set. ∀z ∈ Set. z ∈ y ⟺ (∀w ∈ Set. w ∈ z ⟹ w ∈ x);
apply Pow_axiom[THEN all.elim1, OF x ! !, THEN ex.elim];
- for X if X!, Xspec;
	apply ex1_intro[of X];
	apply Xspec;
	apply all.intro;
	- for X' if X'!, X'spec;
		by set_eq_intro #unfold Xspec[THEN all.elim1] X'spec[THEN all.elim1].
	.
.

obtain Pow where
	Pow_Set! ∀x. x ∈ Set ⟹ Pow x ∈ Set,
	Pow_iff: ∀x y. x ∈ Set ⟹ y ∈ Set ⟹ y ∈ Pow x ⟺ (∀z ∈ Set. z ∈ y ⟹ z ∈ x);
- for thesis if assm;
	apply assm[of (λx. THE X ∈ Set. ∀y ∈ Set. y ∈ X ⟺ (∀z ∈ Set. z ∈ y ⟹ z ∈ x))];
	-; by #unfold(=) beta.
	- for x y if x!, y!;
		unfold(=) beta;
		apply ex1_imp_THE[OF Pow_ex1[OF x] ! !, THEN all.elim1, OF y ! !].
	.
.

---
### Unions
---
assume UN_axiom: ∀x ∈ Set. ∃y ∈ Set. ∀z ∈ Set. z ∈ y ⟺ (∃w ∈ Set. w ∈ x ∧ z ∈ w).

lemma UN_ex1: if x! x ∈ Set then ∃!y ∈ Set. ∀z ∈ Set. z ∈ y ⟺ (∃w ∈ Set. w ∈ x ∧ z ∈ w);
apply UN_axiom[THEN all.elim1, OF x ! !, THEN ex.elim];
- for y if y!, yspec;
	apply ex1_intro[of y];
	apply yspec;
	apply all.intro;
	- for y' if y'!, y'spec;
		apply set_eq_intro;
		- for z if z!;
			unfold yspec[THEN all.elim1] y'spec[THEN all.elim1].
		.
	.
.

obtain (⋃) where
	UN_Set! ∀x. x ∈ Set ⟹ ⋃x ∈ Set,
	UN_iff: ∀x y. x ∈ Set ⟹ y ∈ Set ⟹ y ∈ ⋃x ⟺ (∃z ∈ Set. z ∈ x ∧ y ∈ z);
- for thesis if assm;
	apply assm[of (λx. THE U ∈ Set. ∀y ∈ Set. y ∈ U ⟺ (∃z ∈ Set. z ∈ x ∧ y ∈ z))];
	- for x if x!;
		unfold(=) beta.
	- for x y if x!, y!;
		unfold(=) beta;
		apply ex1_imp_THE[OF UN_ex1[OF x] ! !, THEN all.elim1, OF y ! !].
	.
.

obtain (∪) where
	un_Set! ∀x y. x ∈ Set ⟹ y ∈ Set ⟹ x ∪ y ∈ Set,
	un_iff: ∀x y z. x ∈ Set ⟹ y ∈ Set ⟹ z ∈ Set ⟹ x ∈ y ∪ z ⟺ x ∈ y ∨ x ∈ z;
- for thesis if assm;
	apply assm[of (λy z. ⋃(upair y z))];
	- for x y if x!, y!;
		unfold(=) beta.
	- for x y z if x!, y!, z!;
		unfold(=) beta;
		unfold UN_iff upair_iff;
		apply iff.intro;
		- if ex;
			apply ex.elim[OF ex];
			- for w if !, and;
				apply and.elim[OF and];
				- if or, xw;
					apply or.elim[OF or];
					- if eq: w = y;
						by xw[unfolded eq] #unfold or_iff_true1.
					- if eq: w = z;
						by xw[unfolded eq] #unfold or_iff_true2.
					.
				.
			.
		- if or;
			apply or.elim[OF or];
			-; by and.intro ex.intro1[of y] #unfold or_iff_true1.
			-; by and.intro ex.intro1[of z] #unfold or_iff_true2.
			.
		.
	.
.

---
### Infinity
---
assume infinity_axiom: ∃x ∈ Set. ∅ ∈ x ∧ (∀y ∈ x. y ∪ singleton y).

---
### Replacement
---
assume replacement_axiom:
	if P ∈ Set → Set → Prop
	then (∀x ∈ Set. ∃!y ∈ Set. P x y) ⟹ ∀w ∈ Set. ∃v ∈ Set. ∀r ∈ Set. r ∈ v ⟺ (∃s ∈ Set. s ∈ w ∧ P s r).

print.
lemma replacement_ex1:
	if P! P ∈ Set → Set → Prop, ex1: ∀x ∈ Set. ∃!y ∈ Set. P x y, w! w ∈ Set
	then ∃!v ∈ Set. ∀r ∈ Set. r ∈ v ⟺ (∃s ∈ Set. s ∈ w ∧ P s r);
-- proof
	apply replacement_axiom[OF P ex1, THEN all.elim1, OF w !, THEN ex.elim];
	note! P[THEN fun_elim1, THEN fun_elim1].
	- for v if v! v ∈ Set, in_v: ∀ r ∈ Set. r ∈ v ⟺ (∃ s ∈ Set. s ∈ w ∧ P s r);
		apply+ ex1_intro[of v] all.intro;
		- for x if x! x ∈ Set then x ∈ v ⟺ (∃ s ∈ Set. s ∈ w ∧ P s x);
			by in_v[THEN all.elim1].
		- for x if x! x ∈ Set, in_x: ∀ r ∈ Set. r ∈ x ⟺ (∃ s ∈ Set. s ∈ w ∧ P s r) then x = v;
			by set_eq_intro #unfold in_v[THEN all.elim1] in_x[THEN all.elim1].
		.
	.
-- qed

obtain Replace where
	Replace_type: P ∈ Set → Set → Prop ⟹ (∀x ∈ Set. ∃!y ∈ Set. P x y) ⟹ w ∈ Set ⟹ Replace P w ∈ Set,
	Replace_iff: P ∈ Set → Set → Prop ⟹ (∀x ∈ Set. ∃!y ∈ Set. P x y) ⟹ w ∈ Set ⟹ r ∈ Set ⟹
		r ∈ Replace P w ⟺ (∃s ∈ Set. s ∈ w ∧ P s r);
- for thesis if assm;
	apply assm[of (λP w. THE v ∈ Set. ∀r ∈ Set. r ∈ v ⟺ (∃s ∈ Set. s ∈ w ∧ P s r))];



assume collect_in_iff: (∀x. x ∈ Set ⟹ P.[x] ∈ Prop) ⟹ A ∈ Set ⟹ 

