---
# HOL (Intuitionistic)
---
import STT, TypedUniqueSuch, Typedef.

begin
---
### Encoding of Pairs

Gordon represents a pair of `x : A` and `y : B` by the predicate `fun a : A, b : B. a = x ∧ b = y`.
---

definition MK_PAIR = fun A B : TYPE, x : A, y : B, a : A, b : B. a = x ∧ b = y.

lemma MK_PAIR_type! if [A : TYPE, B : TYPE] then MK_PAIR A B : A → B → A → B → Prop;
	by #simp MK_PAIR_def.
note MK_PAIR_type1! MK_PAIR_type[THEN to_elim1].
note MK_PAIR_type2! MK_PAIR_type1[THEN to_elim1].
note MK_PAIR_type3! MK_PAIR_type2[THEN to_elim1].
note MK_PAIR_type4! MK_PAIR_type3[THEN to_elim1].

definition IS_PAIR = fun A B : TYPE, p : A → B → Prop. ∃x : A, y : B. p = MK_PAIR A B x y.

lemma IS_PAIR_type! if [A : TYPE, B : TYPE] then IS_PAIR A B : (A → B → Prop) → Prop;
	by #simp IS_PAIR_def.

lemma IS_PAIR_MK_PAIR:
	if [A : TYPE, B : TYPE, x : A, y : B] then IS_PAIR A B (MK_PAIR A B x y);
	simp IS_PAIR_def;
	apply ex_intro1[of x], ex_intro1[of y];
	by MK_PAIR_type2[THEN eq_prop1].

lemma MK_PAIR: if [A : TYPE, B : TYPE, x : A, y : B] then MK_PAIR A B x y x y;
	by #simp MK_PAIR_def.

instance prod:
	TypeDefinition (TYPE × TYPE) ((A,B). A → B → Prop) (fun (A,B) : TYPE × TYPE. IS_PAIR A B);
	- if X: X : TYPE × TYPE; apply pair_elim[OF X];
		- if #simp X = (A,B), ... .
		.
	- for thesis if assm;
		apply assm[of (fun (A,B) : TYPE × TYPE. MK_PAIR A B (such x : A. true) (such y : B. true))];
		- if X: X : TYPE × TYPE; apply pair_elim[OF X];
			- if #simp X = (A,B), ...;
				simp IS_PAIR_def;
				apply ex_intro1[of (such x : A. true)], ex_intro1[of (such y : B. true)];
				by eq_prop[of (A → B → Prop)].
			.
		.
	.

definition PROD = fun A B : TYPE. prod.ABS (A,B).

definition COMMA = fun A B : TYPE, x : A, y : B. prod.Abs (A,B) (MK_PAIR A B x y).

definition FST = fun A B : TYPE, p : PROD A B. such x : A. ∃y : B. prod.Rep (A,B) p x y.

definition SND = fun A B : TYPE, p : PROD A B. such y : B. ∃x : A. prod.Rep (A,B) p x y.

lemma PROD_type: PROD : TYPE → TYPE → TYPE; by prod.ABS_type #simp PROD_def.

theory Prod A B :=
	assume A! A : TYPE.
	assume B! B : TYPE.
begin

	lemma PROD_eq_ABS: PROD A B = prod.ABS (A,B); simp PROD_def.

	lemma COMMA_type: COMMA A B : A → B → PROD A B;
		by prod.Abs_type[of (A,B), simp, OF !] #simp COMMA_def PROD_def.

	note! COMMA_type[THEN to_elim1, THEN to_elim1].

	note! prod.Rep_type[of (A,B), simp, OF !, THEN to_elim1, THEN to_elim1, THEN to_elim1].
	note! prod.Abs_type[of (A,B), simp, OF !, THEN to_elim1].
	note! IS_PAIR_MK_PAIR MK_PAIR.

	lemma FST_type: FST A B : PROD A B → A; simp FST_def PROD_def.

	lemma#simp if [IS_PAIR A B p, p : A → B → Prop] then prod.Rep (A,B) (prod.Abs (A,B) p) = p;
		apply prod.Rep_Abs.


	lemma FST_PROD: if [x : A, y : B] then FST A B (COMMA A B x y) = x;
		simp FST_def COMMA_def PROD_def;
		apply the_eq_intro;
		- apply ex_intro1[of y].
		- for x' if ex, ...; apply ex_elim[OF ex];
			- for y' if rep, ...; unfold rep[simp MK_PAIR_def, THEN and_elim1].
			.
		.

	lemma SND_PROD: if [x : A, y : B] then SND A B (COMMA A B x y) = y;
		simp SND_def COMMA_def PROD_def;
		apply the_eq_intro;
		- apply ex_intro1[of x].
		- for y' if ex, ...; apply ex_elim[OF ex];
			- for x' if rep, ...; unfold rep[simp MK_PAIR_def, THEN and_elim2].
			.
		.

end

thm Prod::FST_PROD.

