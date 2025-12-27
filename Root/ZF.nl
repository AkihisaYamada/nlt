---
# Zermelo-Fraenkel Set Theory

We formalize intuitionistic ZF set theory in a conservative axiomatic form.
There, operations to derive sets from others are not explicit, but
only the existence of the resulting sets is axiomatized.

We base on equational intuitionistic FOL.
---
import Eq.
import FOL.
import Intuitionistic.

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
assume ext_axiom: ∀A ∈ Set. ∀B ∈ Set. (∀x ∈ Set. x ∈ A ⟺ x ∈ B) ⟹ A = B.

---
As an inference rule:
---
lemma ext: for A B if eq: ∀x. x ∈ Set ⟹ x ∈ A ⟺ x ∈ B, A! A ∈ Set, B! B ∈ Set then A = B;
	note 1: all_elim1[OF ext_axiom A ! !].
	apply all_elim1[OF 1 B ! !];
	by all_intro eq.

---
### Empty set

The empty set is specified by an existential axiom (of type `Prop`):
---
assume empty_axiom: ∃x ∈ Set. ¬(∃y ∈ Set. y ∈ x).

obtain ∅ where empty_Set! ∅ ∈ Set, nex_in_empty: ¬(∃x ∈ Set. x ∈ ∅);
	for thesis if assm;
	apply ex_elim[OF empty_axiom];
		for e;
			by assm[of e].
	.
.

---
### Unordered pairs

We need to admit more for more constructions;
for instance, the unordered pair $\{x,y\}$ is axiomatized by
---
assume upair_axiom: ∀x ∈ Set. ∀y ∈ Set. ∃z ∈ Set. ∀w ∈ Set. w ∈ z ⟺ w = x ∨ w = y.
---
Informally, then one would assume granted a binary operator which,
given `x` and `y` as arguments, denotes the (unique) `z`.

In Naive Logic, such a binary function is not possible without further assumptions.
For given `x` and `y`, we can use the unique choice operator to denote the `z`:
---
import Intuitionistic.UniqueChoiceOp.
---
Now what one assumes is further a function such that `upair x y = (THE z. ...)`.
We achieve this by admitting the (untyped) lambda calculus:
take `λx y. THE z. ...` as `upair`.
---
import Lambda.

note! ex1_type THE_type.

note(cong) iff.ex1_cong.

lemma upair_ex1:
	if x! x ∈ Set, y! y ∈ Set then ∃!z ∈ Set. ∀w ∈ Set. w ∈ z ⟺ w = x ∨ w = y;
apply upair_axiom[THEN all_elim1, OF x ! !, THEN all_elim1, OF y ! !, THEN ex_elim];
	for z if !, zall;
		apply ex1_intro[of z];
		apply zall;
		apply all_intro;
		for z' if !, z'all;
			apply ext;
			for w if w!;
				unfold z'all[THEN all_elim1] zall[THEN all_elim1].
		.
	.
.

obtain upair where
	upair_Set! ∀x y. x ∈ Set ⟹ y ∈ Set ⟹ upair x y ∈ Set,
	upair_iff: ∀x y z. x ∈ Set ⟹ y ∈ Set ⟹ z ∈ Set ⟹ z ∈ upair x y ⟺ z = x ∨ z = y;
	for thesis if assm;
		apply assm[of (λx y. THE z ∈ Set. ∀w ∈ Set. w ∈ z ⟺ w = x ∨ w = y)];
		for x y if !, !;
			unfold(=) beta.
		for x y z if x!, y!, z!;
			unfold(=) beta;
			by ex1_imp_THE[OF upair_ex1[OF x y] ! !, THEN all_elim1, OF z ! !].
		by #unfold(=) beta.
	by #unfold(=) beta.

obtain singleton where
	singleton_Set! ∀x. x ∈ Set ⟹ singleton x ∈ Set,
	singleton_iff: ∀x y. x ∈ Set ⟹ y ∈ Set ⟹ y ∈ singleton x ⟺ x = y;
	for thesis if assm;
		apply assm[of (λx. upair x x)];
		for x if x!;
			unfold(=) beta.
		for x y if x!, y!;
			unfold(=) beta;
			unfold upair_iff iff.or.idem;
			apply iff_intro;
			if xy;
				by #unfold xy.
			if yx;
				by #unfold yx.
			.
		.
	.

assume Pow_axiom: ∀x ∈ Set. ∃y ∈ Set. ∀z ∈ Set. z ∈ y ⟺ (∀w ∈ Set. w ∈ z ⟹ w ∈ x).

lemma Pow_ex1: if x! x ∈ Set then ∃!y ∈ Set. ∀z ∈ Set. z ∈ y ⟺ (∀w ∈ Set. w ∈ z ⟹ w ∈ x);
	apply Pow_axiom[THEN all_elim1, OF x ! !, THEN ex_elim];
	for X if X!, Xspec;
		apply ex1_intro[of X];
		apply Xspec;
		apply all_intro;
		for X' if X'!, X'spec;
			by ext #unfold Xspec[THEN all_elim1] X'spec[THEN all_elim1].
		.
	.

obtain Pow where
	Pow_Set! ∀x. x ∈ Set ⟹ Pow x ∈ Set,
	Pow_iff: ∀x y. x ∈ Set ⟹ y ∈ Set ⟹ y ∈ Pow x ⟺ (∀z ∈ Set. z ∈ y ⟹ z ∈ x);
	for thesis if assm;
		apply assm[of (λx. THE X ∈ Set. ∀y ∈ Set. y ∈ X ⟺ (∀z ∈ Set. z ∈ y ⟹ z ∈ x))];
		- by #unfold(=) beta.
		for x y if x!, y!;
			unfold(=) beta;
			apply ex1_imp_THE[OF Pow_ex1[OF x] ! !, THEN all_elim1, OF y ! !].
		.
	.

assume UN_axiom: ∀x ∈ Set. ∃y ∈ Set. ∀z ∈ Set. z ∈ y ⟺ (∃w ∈ Set. w ∈ x ∧ z ∈ w).

lemma UN_ex1: if x! x ∈ Set then ∃!y ∈ Set. ∀z ∈ Set. z ∈ y ⟺ (∃w ∈ Set. w ∈ x ∧ z ∈ w);
	apply UN_axiom[THEN all_elim1, OF x ! !, THEN ex_elim];
	for y if y!, yspec;
		apply ex1_intro[of y];
		apply yspec;
		apply all_intro;
		for y' if y'!, y'spec;
			apply ext;
			for z if z!;
				unfold yspec[THEN all_elim1] y'spec[THEN all_elim1].
			.
		.
	.

obtain (⋃) where
	UN_Set! ∀x. x ∈ Set ⟹ ⋃x ∈ Set,
	UN_iff: ∀x y. x ∈ Set ⟹ y ∈ Set ⟹ y ∈ ⋃x ⟺ (∃z ∈ Set. z ∈ x ∧ y ∈ z);
	for thesis if assm;
		apply assm[of (λx. THE U ∈ Set. ∀y ∈ Set. y ∈ U ⟺ (∃z ∈ Set. z ∈ x ∧ y ∈ z))];
		for x if x!;
			unfold(=) beta.
		for x y if x!, y!;
			unfold(=) beta;
			apply ex1_imp_THE[OF UN_ex1[OF x] ! !, THEN all_elim1, OF y ! !].
		.
	.

assume infinite_axiom: ∃x ∈ Set. ∅ ∈ x ∧ (∀y ∈ x. ⋃(upair y (upair y y))).

assume collect_in_iff: (∀x. x ∈ Set ⟹ P.[x] ∈ Prop) ⟹ A ∈ Set ⟹ 

