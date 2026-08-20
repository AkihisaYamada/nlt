---
# Defining `Bool`

Gordon's HOL uses type `bool` for propositions and assumes that true and false are the only inhabitants.
We do not have to assume this on `Prop`, and one can define a two-valued type.
---
import UniqueSuchTyped, Typedef.

begin

instance Bool: TypeDefinition TYPE (x. Prop) (fun _ : TYPE, p : Prop. p = true ∨ p = false);
	- .
	- for thesis if assm then thesis;
		apply assm[of (fun _ : TYPE. true)];
		by or_intro1 eq_prop[of Prop].
	.

definition Bool = Bool.ABS Prop.
definition bool = fun p : Prop. Bool.Abs Prop (IF Prop p true false).
definition Trueprop = Bool.Rep Prop.
definition True = bool true.
definition False = bool false.

note! Bool.Abs_type1[of Prop, OF !]
	  Bool.ABS_type1[of Prop, OF !]
	  Bool.Rep_type1[for a, of Prop a, fold Bool_def, OF !].

lemma Bool_TYPE! Bool : TYPE; unfold Bool_def.

lemma bool_type! if [p : Prop] then bool p : Bool;
	simp bool_def Bool_def.

lemma True_type! True : Bool; simp True_def.

lemma False_type! False : Bool; simp False_def.

lemma eq_true_imp: if p1: p = true then p; unfold p1.

lemma Trueprop_type! Trueprop : Bool → Prop;
	unfold Trueprop_def Bool_def; apply Bool.Rep_type.

note Trueprop_type1! Trueprop_type[THEN to_elim1].

lemma Trueprop_bool_decided:
	if dec: p ∨ ¬p, [p : Prop] then Trueprop (bool p) = IF Prop p true false;
-	simp bool_def Trueprop_def;
	apply Bool.Rep_Abs; -. -.
	simp;
	apply or_elim[OF dec];
	- if p; by #simp IF_then[OF p] #intro eq_prop[of Prop] or_intro1.
	- if np; by #simp IF_not[OF np] #intro eq_prop[of Prop] or_intro2.
	by eq_prop[of Prop].
.
	
lemma Trueprop! if p: p, [p : Prop] then Trueprop (bool p);
	apply Trueprop_bool_decided[THEN eq_imp_rev];
	by or_intro1 p #simp IF_then.

lemma Trueprop_not! if np: ¬p, [p : Prop] then ¬ Trueprop (bool p);
	apply Trueprop_bool_decided[THEN eq_elim2, of (x. ¬x)];
	by np or_intro2 #simp IF_else.

lemma Trueprop_True#simp Trueprop True = true;
	.. = IF Prop true true false;
		unfold True_def; apply Trueprop_bool_decided, or_intro1.
	.

lemma Trueprop_false#simp Trueprop False = false;
	.. = IF Prop false true false;
		unfold False_def; apply Trueprop_bool_decided, or_intro2.
	.

instance Bool: Std.Prop Bool;
	- apply to_elim1=.
	.

lemma Bool_cases: if 1: b = True ⟹ P, 0: b = False ⟹ P, b! b : Bool, [P : Prop] then P;
	have Abs_Rep: Bool.Abs Prop (Bool.Rep Prop b) = b;
		apply Bool.Abs_Rep[of Prop, OF ! b[unfold Bool_def]].
	apply Bool.Rep[OF b[unfold Bool_def], simp, THEN or_elim];
	- if 1': Bool.Rep Prop b = true;
		apply 1;
		fold Abs_Rep;
		simp 1' True_def bool_def.
	- if 0': Bool.Rep Prop b = false;
		apply 0;
		fold Abs_Rep;
		simp 0' False_def bool_def.
	by eq_prop[of Prop].

lemma Trueprop_imp_eq: if x: Trueprop x, [x : Bool] then x = True;
	apply Bool_cases[of x];
	-.
	- if #simp x = False; use x; by #elim false_elim.
	.

lemma Trueprop_iff_Trueprop_elim:
	if iff: Trueprop x ⟷ Trueprop y, [x : Bool, y : Bool] then x = y;
	apply Bool_cases[of x];
	- if x1; 
		apply Bool_cases[of y];
		- if y1; unfold x1 y1.
		- if y0;
			have y: Trueprop y; fold[on (⟷)] iff; simp x1.
			use y; by #simp y0 #elim false_elim.
		.
	- if x0;
		apply Bool_cases[of y];
		- if y1;
			have x: Trueprop x; unfold[on (⟷)] iff; simp y1.
			use x; by #simp x0 #elim false_elim.
		- if y0; unfold x0 y0.
		.
	.

definition Bool_case =
	fun 'a : TYPE, t : 'a, f : 'a, x : Bool. IF 'a (Trueprop x) t f.

lemma Bool_case_type! if ['a : TYPE] then Bool_case 'a : 'a → 'a → Bool → 'a;
	by #simp Bool_case_def.

note Bool_case_type1! Bool_case_type[THEN to_elim1].
note Bool_case_type2! Bool_case_type1[THEN to_elim1].
note Bool_case_type3! Bool_case_type2[THEN to_elim1].

lemma Bool_case_True#simp
	if ['a : TYPE, t : 'a, f : 'a] then Bool_case 'a t f True = t;
	simp Bool_case_def.

lemma Bool_case_False#simp
	if ['a : TYPE, t : 'a, f : 'a] then Bool_case 'a t f False = f;
	simp Bool_case_def.

instance Bool: Equality Bool.

definition[as AND] (&&) =
	Bool_case (Bool → Bool) (fun y : Bool. y) (fun y : Bool. False).

definition[as OR] (||) =
	Bool_case (Bool → Bool) (fun y : Bool. True) (fun y : Bool. y).

instance OR: Bool.BooleanAlgebra (||) (&&) True False;
	note! Bool_case_type3[THEN to_elim1] eq_prop[of Bool, OF !].
	show! if [x : Bool, y : Bool] then (x || y) : Bool; by #simp OR_def.
	- if [x : Bool, y : Bool, z : Bool] then (x || y || z) = (x || (y || z));
		unfold OR_def;
		apply Bool_cases[of x];
		- if #simp.
		- if #simp.
		by eq_prop[of Bool].
	- if [x : Bool, y : Bool] then (x || y) = (y || x);
		unfold OR_def;
		apply Bool_cases[of x];
		- if #simp; apply Bool_cases[of y];
			- if #simp.
			- if #simp.
			.
		- if #simp; apply Bool_cases[of y];
			- if #simp.
			- if #simp.
			.
		by eq_prop[of Bool].
	- if #simp y = y', [x : Bool], ... then (x || y) = (x || y').
	show or0#simp if [x : Bool] then (False || x) = x; simp OR_def.
	show or1#simp if [x : Bool] then (True || x) = True; simp OR_def.
	- if [x : Bool] then (x || x) = x; apply Bool_cases[of x];
		- if #simp.
		- if #simp.
		.
	show! if [x : Bool, y : Bool] then (x && y) : Bool;
		by #simp AND_def.
	- if [x : Bool, y : Bool, z : Bool] then (x && y && z) = (x && (y && z));
		unfold AND_def;
		apply Bool_cases[of x];
		- if #simp.
		- if #simp.
		by eq_prop[of Bool].
	- if [x : Bool, y : Bool] then (x && y) = (y && x);
		unfold AND_def;
		apply Bool_cases[of x];
		- if #simp; apply Bool_cases[of y];
			- if #simp.
			- if #simp.
			.
		- if #simp; apply Bool_cases[of y];
			- if #simp.
			- if #simp.
			.
		by eq_prop[of Bool].
	- if #simp y = y', [x : Bool], ... then (x && y) = (x && y').
	show and1#simp if [x : Bool] then (True && x) = x; simp AND_def.
	show and0#simp if [x : Bool] then (False && x) = False; simp AND_def.
	- if [x : Bool] then (x && x) = x; apply Bool_cases[of x];
		- if #simp.
		- if #simp.
		.
	- if [x : Bool, y : Bool, z : Bool] then (x || y && z) = ((x || y) && (x || z));
		apply Bool_cases[of x];
		- if #simp.
		- if #simp.
		.
	- if [x : Bool, y : Bool] then (x || x && y) = x;
		apply Bool_cases[of x];
		- if #simp.
		- if #simp.
		.
	- if [x : Bool, y : Bool, z : Bool] then (x && (y || z)) = ((x && y) || (x && z));
		apply Bool_cases[of x];
		- if #simp.
		- if #simp.
		.
	- if [x : Bool, y : Bool] then (x && (x || y)) = x;
		apply Bool_cases[of x];
		- if #simp.
		- if #simp.
		.
	.

note! OR.closed OR.dual.closed.

instance AND: Bool.BooleanAlgebra (&&) (||) False True;
	by OR.dual.left_assoc OR.dual.commute OR.dual.left_mono OR.dual.left_neutral OR.dual.left_absorb OR.dual.idem
		OR.left_assoc OR.commute OR.left_mono OR.left_neutral OR.left_absorb OR.idem
		OR.dual.left_distrib OR.dual.left_absorptive
		OR.left_distrib OR.left_absorptive.