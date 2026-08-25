
lemma Bool_cases: if 1: b = True ⟹ P, 0: b = False ⟹ P, b! b : Bool, [P : Prop] then P;
	have abs_rep: Bool.abs Prop (Bool.rep Prop b) = b;
		apply Bool.abs_rep[of Prop, OF ! b[unfold Bool_def]].
	apply Bool.rep[OF b[unfold Bool_def], simp, THEN or_elim];
	- if 1': Bool.rep Prop b = true;
		apply 1;
		fold abs_rep;
		simp 1' True_def bool_def.
	- if 0': Bool.rep Prop b = false;
		apply 0;
		fold abs_rep;
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

