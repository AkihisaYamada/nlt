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

note! Bool.Abs_type1[of Prop, OF !]
	  Bool.ABS_type1[of Prop, OF !]
	  Bool.Rep_type1[for a, of Prop a, fold Bool_def, OF !].

lemma Bool_TYPE! Bool : TYPE; unfold Bool_def.

lemma bool_type! if [p : Prop] then bool p : Bool;
	simp bool_def Bool_def.

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

lemma Trueprop_true#simp Trueprop (bool true) = true;
	.. = IF Prop true true false;
		apply Trueprop_bool_decided, or_intro1.
	.

lemma Trueprop_false#simp Trueprop (bool false) = false;
	.. = IF Prop false true false;
		apply Trueprop_bool_decided, or_intro2.
	.

instance Bool: Std.Prop Bool;
	- apply to_elim1=.
	.

lemma Bool_cases: if 1: b = bool true ⟹ P, 0: b = bool false ⟹ P, b! b : Bool, [P : Prop] then P;
	have Abs_Rep: Bool.Abs Prop (Bool.Rep Prop b) = b;
		apply Bool.Abs_Rep[of Prop, OF ! b[unfold Bool_def]].
	apply Bool.Rep[OF b[unfold Bool_def], simp, THEN or_elim];
	- if 1': Bool.Rep Prop b = true;
		apply 1;
		fold Abs_Rep;
		simp 1' bool_def.
	- if 0': Bool.Rep Prop b = false;
		apply 0;
		fold Abs_Rep;
		simp 0' bool_def.
	by eq_prop[of Prop].

lemma Trueprop_imp_eq: if x: Trueprop x, [x : Bool] then x = bool true;
	apply Bool_cases[of x];
	-.
	- if #simp x = bool false; use x; by #elim false_elim.
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
