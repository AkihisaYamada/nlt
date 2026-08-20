---
# Defining Product Types
---
import Typedef.

---
In Gordon's encoding of pairs, the (unique) choice operator is essential.
---
import UniqueSuchTyped.

begin
---
### Encoding of Pairs

Gordon represents a pair of `x : 'a` and `y : 'b` by the predicate `fun a : 'a, b : 'b. a = x ∧ b = y`.
---

definition MK_PAIR = fun 'a 'b : TYPE, x : 'a, y : 'b, a : 'a, b : 'b. a = x ∧ b = y.

lemma MK_PAIR_type! if ['a : TYPE, 'b : TYPE] then MK_PAIR 'a 'b : 'a → 'b → 'a → 'b → Prop;
	by #simp MK_PAIR_def.
note MK_PAIR_type1! MK_PAIR_type[THEN to_elim1].
note MK_PAIR_type2! MK_PAIR_type1[THEN to_elim1].
note MK_PAIR_type3! MK_PAIR_type2[THEN to_elim1].
note MK_PAIR_type4! MK_PAIR_type3[THEN to_elim1].

definition IS_PAIR = fun 'a 'b : TYPE, p : 'a → 'b → Prop. ∃x : 'a, y : 'b. p = MK_PAIR 'a 'b x y.

lemma IS_PAIR_type! if ['a : TYPE, 'b : TYPE] then IS_PAIR 'a 'b : ('a → 'b → Prop) → Prop;
	by #simp IS_PAIR_def.

lemma IS_PAIR_MK_PAIR:
	if ['a : TYPE, 'b : TYPE, x : 'a, y : 'b] then IS_PAIR 'a 'b (MK_PAIR 'a 'b x y);
	simp IS_PAIR_def;
	apply ex_intro1[of x], ex_intro1[of y];
	by MK_PAIR_type2[THEN eq_prop1].

lemma MK_PAIR: if ['a : TYPE, 'b : TYPE, x : 'a, y : 'b] then MK_PAIR 'a 'b x y x y;
	by #simp MK_PAIR_def.

instance prod:
	TypeDefinition (TYPE × TYPE) (('a,'b). 'a → 'b → Prop) (fun ('a,'b) : TYPE × TYPE. IS_PAIR 'a 'b);
	- if X: X : TYPE × TYPE; apply prod_pair_elim[OF X].
	- for thesis if assm;
		apply assm[of (fun ('a,'b) : TYPE × TYPE. MK_PAIR 'a 'b (such x : 'a. true) (such y : 'b. true))];
		- if X: X : TYPE × TYPE; apply prod_pair_elim[OF X];
			- if ['a : TYPE, 'b : TYPE];
				simp IS_PAIR_def;
				apply ex_intro1[of (such x : 'a. true)], ex_intro1[of (such y : 'b. true)];
				by eq_prop[of ('a → 'b → Prop)].
			.
		.
	.

definition PROD = fun 'a 'b : TYPE. prod.ABS ('a,'b).

definition COMMA = fun 'a 'b : TYPE, x : 'a, y : 'b. prod.Abs ('a,'b) (MK_PAIR 'a 'b x y).

definition FST = fun 'a 'b : TYPE, p : PROD 'a 'b. such x : 'a. ∃y : 'b. prod.Rep ('a,'b) p x y.

definition SND = fun 'a 'b : TYPE, p : PROD 'a 'b. such y : 'b. ∃x : 'a. prod.Rep ('a,'b) p x y.

definition PROD_CASES = fun 'a 'b 'c : TYPE, f : 'a → 'b → 'c, p : PROD 'a 'b. f (FST 'a 'b p) (SND 'a 'b p).

lemma PROD_type! PROD : TYPE → TYPE → TYPE; by prod.ABS_type #simp PROD_def.

note PROD_type1! PROD_type[THEN to_elim1].
note PROD_type2! PROD_type1[THEN to_elim1].

theory PROD :=
	fix 'a. assume 'a! 'a : TYPE.
	fix 'b. assume 'b! 'b : TYPE.
begin

	lemma ABS_eq_PROD: prod.ABS ('a,'b) = PROD 'a 'b; simp PROD_def.

	lemma COMMA_type: COMMA 'a 'b : 'a → 'b → PROD 'a 'b;
		by prod.Abs_type[of ('a,'b), simp, OF !] #simp COMMA_def PROD_def.

	note! COMMA_type[THEN to_elim1, THEN to_elim1].

	note Rep_type0! prod.Rep_type[of ('a,'b), simp ABS_eq_PROD, OF !].
	note Rep_type1! Rep_type0[THEN to_elim1].
	note Rep_type2! Rep_type1[THEN to_elim1].
	note! Rep_type2[THEN to_elim1].
	note! prod.Abs_type[of ('a,'b), simp ABS_eq_PROD, OF !, THEN to_elim1].
	note! IS_PAIR_MK_PAIR MK_PAIR.

	lemma FST_type! FST 'a 'b : PROD 'a 'b → 'a; simp FST_def.

	lemma SND_type! SND 'a 'b : PROD 'a 'b → 'b; simp SND_def.

	lemma Rep_Abs#simp
		if [IS_PAIR 'a 'b p, p : 'a → 'b → Prop] then prod.Rep ('a,'b) (prod.Abs ('a,'b) p) = p;
		apply prod.Rep_Abs.

	lemma FST: if [x : 'a, y : 'b] then FST 'a 'b (COMMA 'a 'b x y) = x;
		simp FST_def COMMA_def;
		apply such_eq_intro;
		- apply ex_intro1[of y].
		- for x' if ex, ...; apply ex_elim[OF ex];
			- for y' if rep, ...; unfold rep[simp MK_PAIR_def, THEN and_elim1].
			.
		.

	lemma SND: if [x : 'a, y : 'b] then SND 'a 'b (COMMA 'a 'b x y) = y;
		simp SND_def COMMA_def;
		apply such_eq_intro;
		- apply ex_intro1[of x].
		- for y' if ex, ...; apply ex_elim[OF ex];
			- for x' if rep, ...; unfold rep[simp MK_PAIR_def, THEN and_elim2].
			.
		.

	lemma IS_PAIR: if [p : PROD 'a 'b] then IS_PAIR 'a 'b (prod.Rep ('a,'b) p);
		apply prod.Rep[of p ('a,'b), simp ABS_eq_PROD, OF ! !].

	lemma Abs_Rep#simp if [p : PROD 'a 'b] then prod.Abs ('a,'b) (prod.Rep ('a,'b) p) = p;
		apply prod.Abs_Rep; by #simp ABS_eq_PROD.

	lemma cases:
		if p! p : PROD 'a 'b,
		   assm: ∀x y. p = COMMA 'a 'b x y ⟹ x : 'a ⟹ y : 'b ⟹ P,
		   [P : Prop]
		then P;
		note! Rep_type1[OF p].-- because `prod.Rep ('a,'b) p = ... : Prop` is necessary
		apply IS_PAIR[OF p, simp IS_PAIR_def, THEN ex_elim];
		- for x if exy, ...;
			apply exy[THEN ex_elim];
			- for y if eq: prod.Rep ('a, 'b) p = MK_PAIR 'a 'b x y, ...;
				apply assm[of x y]; simp COMMA_def eq[dual].
			.
		.

	instance Abs: Inversive (prod.Rep ('a,'b)) (prod.ABS ('a,'b)) (prod.Abs ('a,'b));
		by prod.Abs_Rep.

	lemma exhaust: if p! p : PROD 'a 'b then COMMA 'a 'b (FST 'a 'b p) (SND 'a 'b p) = p;
		apply cases[OF p];
		- if eq: p = COMMA 'a 'b x y, ...;
			simp eq FST SND.
		.

end

thm PROD/FST.
thm PROD/SND.

