---
## Type Definition Mechanism

The type definition machineries of HOL proof assistants a la Gordon[^Gordon1988] are
the key for Church's simple type theory to be expressive enough for daily mathematics.

[^Gordon1988]
	Michael JC Gordon. HOL: A proof generating system for higher-order logic.
	VLSI specification, verification and synthesis. 1988. 73-128.

Type definition allows to turn a polymorphic predicate `p : A.[X...] → Prop`
into a new parametric type `B X...` accomponied by
- `Abs_B : A.[X...] → B X...` and
- `Rep_B : B X... → A.[X...]`,
such that
- if `a : A.[X...]` and `p a` then `Rep_B (Abs_B a) = a`; and
- if `b : B X...` then `p (Rep_B x)` and `Abs_B (Rep_B x) = x`.

A straightforward formalization of the above description would require a machinery to represent unbindings with multiple variables.
Postulating syntactic pairs would achieve this, but it is a HOL tradition to define pairs via type definition.

Note that *local* type definitions[^KuncarP2019] are allowed.
[^KuncarP2019]
	Ondřej Kunčar, Andrei Popescu. From Types to Sets by Local Type Definition in Higher-Order Logic.
	Journal of Automated Reasoning 62.2 (2019): 237-260.

---
assume typedef:
	if pred witness,
	   ∀ABS Abs Rep.
		ABS : TYPE → TYPE ⟹
		(∀X. X : TYPE ⟹ Abs : X → ABS X) ⟹
		(∀X. X : TYPE ⟹ Rep : ABS X → X) ⟹
		(∀X. X : TYPE ⟹ ∀a. a : ABS X ⟹ pred (Rep a)) ⟹
		(∀X. X : TYPE ⟹ ∀a. a : ABS X ⟹ Abs (Rep a) = a) ⟹
		(∀X. X : TYPE ⟹ ∀x. x : X ⟹ pred x ⟹ Rep (Abs x) = x) ⟹ thesis
	then thesis.

begin

theory TypeDefinition pred :=
	assume nonempty: if ∀witness. pred witness ⟹ Q then Q.
begin

	obtain tp where tp_spec:
		if	ABS = tp (fun x y z. x),
			Abs = tp (fun x y z. y),
			Rep = tp (fun x y z. z),
			ABS : TYPE → TYPE ⟹
			(∀X. X : TYPE ⟹ Abs : X → ABS X) ⟹
			(∀X. X : TYPE ⟹ Rep : ABS X → X) ⟹
			(∀X. X : TYPE ⟹ ∀a. a : ABS X ⟹ pred (Rep a)) ⟹
			(∀X. X : TYPE ⟹ ∀a. a : ABS X ⟹ Abs (Rep a) = a) ⟹
			(∀X. X : TYPE ⟹ ∀x. x : X ⟹ pred x ⟹ Rep (Abs x) = x) ⟹ Q
		then Q;
	- for thesis if assm;
		apply nonempty;
		- if witness: pred witness;
			apply typedef[OF witness];
			- for ABS0 Abs0 Rep0 if ABS_type!, Abs_type, Rep_type, Rep, Abs_Rep, Rep_Abs;
				apply assm[of (fun i. i ABS0 Abs0 Rep0)];
				- for ABS if ABS1 for Abs if Abs1 for Rep if Rep1 for Q if assm2;
					apply assm2;
					have#simp ABS = ABS0;
						unfold ABS1;
						apply fun_app_eq[OF _ ABS_type];
						have 1: (fun x y z. x) ABS0 = fun y z. ABS0;
							apply ABS_type[THEN fun_indep_to[THEN fun_indep_to, THEN fun_app_eq[OF > _]]].
						unfold 1;
						unfold fun_indep[OF fun_indep_to[OF ABS_type], of id id];
						unfold fun_indep[OF ABS_type, of id].
					have#simp[after 1] if X! X : TYPE V then Abs = Abs0;
						unfold Abs1;
						apply fun_app_eq[OF _ Abs_type[OF X]];
						have 1: (fun x y z. y) ABS0 = fun y z. y;
							apply fun_app[for A B, of (A → B → A)].
						unfold 1;
						have 2: (fun y z. y) Abs0 = fun z. Abs0;
							apply fun_app_eq[OF _ fun_indep_to[OF Abs_type[OF X]]].
						unfold 2;
						unfold fun_indep[OF Abs_type[OF X]].
					have#simp[after 1] if X! X : TYPE V then Rep = Rep0;
						unfold Rep1;
						apply fun_app_eq[OF _ Rep_type[OF X]];
						have 1: (fun x y z. z) ABS0 = (fun y z. z);
							apply fun_app[for A B, of (A → B → B)].
						unfold 1;
						have 2: (fun y z. z) Abs0 = (fun z. z);
							apply fun_app[for B, of (B → B)].
						unfold 2;
						apply fun_app_eq[OF _ Rep_type[OF X]].
					- .
					- by #intro[after 1] Abs_type.
					- by #intro[after 1] Rep_type.
					- by #intro[after 1] Rep.
					- by #intro[after 1] Abs_Rep.
					- by #intro[after 1] Rep_Abs.
					.
				.
			.
		.
	.

	definition ABS = tp (fun x y z. x).
	definition Abs = tp (fun x y z. y).
	definition Rep = tp (fun x y z. z).

	lemma ABS_type: ABS : TYPE V → TYPE V;
		apply tp_spec[OF ABS_def Abs_def Rep_def].

	lemma Abs_type: if X: X : TYPE V then Abs : X → ABS X;
		apply tp_spec[OF ABS_def Abs_def Rep_def];
		- if 1, 2, 3, 4, 5, 6;
			by 2[OF X].
		.

	lemma Rep_type: if X: X : TYPE V then Rep : ABS X → X;
		apply tp_spec[OF ABS_def Abs_def Rep_def];
		- if 1, 2, 3, 4, 5, 6;
			by 3[OF X].
		.

	lemma Abs: if X: X : TYPE V, a: a : ABS X then pred (Rep a);
		apply tp_spec[OF ABS_def Abs_def Rep_def];
		- if 1, 2, 3, 4, 5, 6;
			by 4[OF X a].
		.

	lemma Abs_Rep: if X: X : TYPE V, a: a : ABS X then Abs (Rep a) = a;
		apply tp_spec[OF ABS_def Abs_def Rep_def];
		- if 1, 2, 3, 4, 5, 6;
			by 5[OF X a].
		.

	lemma Rep_Abs: if X: X : TYPE V, x: x : X, px: pred x then Rep (Abs x) = x;
		apply tp_spec[OF ABS_def Abs_def Rep_def];
		- if 1, 2, 3, 4, 5, 6;
			by 6[OF X x px].
		.

end

---
### Pairs

One can encode a pair of `x` and `y` as a higher-order function `fun p. p x y`.
---

interpret prod! TypeDefinition (fun f. true);
	- for Q if assm; by assm[of id].
	.

define[as prod] (×) = fun X Y. prod.ABS (X → Y → Prop).
define[as pair] (,) = fun x y. prod.Abs (fun z. z x y).
define fst = fun p. prod.Rep p (fun x y. x).
define snd = fun p. prod.Rep p (fun x y. y).

lemma prod_type: if X: X : TYPE V, Y: Y : TYPE V then X × Y : TYPE V;
	


obtain pair_tp where tp_spec:
	if  (,) = pair_tp (fun x y z. x),
		fst = pair_tp (fun x y z. y),
		snd = pair_tp (fun x y z. z),
		(∀A B x y. x : A ⟹ y : B ⟹ fst (x,y) = x) ⟹
		(∀A B x y. x : A ⟹ y : B ⟹ snd (x,y) = y) ⟹ P
	then P;

	- for thesis if assm;

		define raw_pair = fun x y i. i x y.
		define raw_fst = fun p. p const.
		define raw_snd = fun p. p (fun x y. y).

		have raw_pair_type! raw_pair : A → B → (A → B → C) → C;
			unfold raw_pair_def.
		have raw_fst_type! raw_fst : ((A → B → A) → A) → A;
			unfold raw_fst_def.
		have raw_snd_type! raw_snd : ((A → B → B) → B) → B;
			unfold raw_snd_def.
		have raw_prod_type: raw_prod : 

		have raw_pair_app: if x! x : A then raw_pair x = fun y i. i x y;
			unfold raw_pair_def;
			apply fun_app[for B C, of (B → (A → B → C) → C)].

		have raw_pair_app2: if x! x : A, y! y : B then raw_pair x y = fun i. i x y;
			unfold raw_pair_app[OF x];
			apply fun_app[for C, of ((A → B → C) → C)].

		have raw_pair_app3: if x! x : A, y! y : B, i! i : A → B → C then raw_pair x y i = i x y;
			unfold raw_pair_app2[OF x y];
			unfold fun_app[of C].

		apply assm[of (fun p. p raw_pair raw_fst raw_snd raw_prod)];
		- for (,) if pair0 for fst if fst0 for snd if snd0 for (×) if prod0 for P if assm2;
			apply assm2;
			have pair: (,) = raw_pair;
				unfold pair0;
				apply in_fun_app_eq[OF raw_pair_type];
				have 1: (fun x y z w. x) raw_pair = fun y z w. raw_pair;
					apply in_fun_app_eq[for A B C D E, of (D → E → A → B → (A → B → C) → C)].
				unfold 1;
				have 2: (fun y z. raw_pair) raw_fst = fun z. raw_pair;
					apply in_fun_app_eq[for A B C E, of (E → A → B → (A → B → C) → C)].
				unfold 2;
				apply in_fun_app_eq[OF raw_pair_type].
			have fst: fst = raw_fst;
				unfold fst0;
				apply in_fun_app_eq[OF raw_fst_type];
				have 1: (fun x y z. y) raw_pair = fun y z. y;
					apply fun_app[for A B, of (A → B → A)].
				unfold 1;
				have 2: (fun y z. y) raw_fst = fun z. raw_fst;
					apply fun_app[for A B C, of (C → ((A → B → A) → A) → A)].
				unfold 2;
				apply fun_app[OF raw_fst_type].
			have snd: snd = raw_snd;
				unfold snd0;
				apply in_fun_app_eq[OF raw_snd_type];
				have 1: (fun x y z. z) raw_pair = fun y z. z;
					apply fun_app[for A B, of (A → B → A)].
				unfold 1;
				have 2: (fun y z. z) raw_fst = fun z. z;
					apply fun_app[for A, of (A → A)].
				unfold 2;
				apply in_fun_app_eq[OF raw_snd_type].
			- for A B x y if x!, y! then fst (x,y) = x;
				unfold pair fst raw_fst_def;
				apply fun_app_eq[of A];
				unfold raw_pair_app3[OF x y const_type].
			- for A B x y if x!, y! then snd (x,y) = y;
				unfold pair snd raw_snd_def;
				apply fun_app_eq[of B];
				have ty: (fun x y. y) : A → B → B.
				unfold raw_pair_app3[OF x y ty];
				unfold fun_app[of (B → B)];
				unfold fun_app[of B].
			.
		.
	.

define[as pair] (,) = pair_tp (fun x y z w. x).
define fst = pair_tp (fun x y z w. y).
define snd = pair_tp (fun x y z w. z).
define[as prod] (×) = pair_tp (fun x y z w. w).

interpret Pair;
	note spec: tp_spec[OF pair_def fst_def snd_def].
	- apply spec;
		- if fst, snd, x: x : A, y: y : B; by fst[OF x y].
		.
	- apply spec;
		- if fst, snd, x: x : A, y: y : B; by snd[OF x y].
		.
	.

thm fst_pair.
