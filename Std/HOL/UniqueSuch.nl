---
# Unique Choice Operator
---

import SuchSignature.
assume unique_such_axiom: if 'a : TYPE then
	∀P : 'a ⇒ Prop. ∀x : 'a. P x ⟶ (∀y : 'a. P y ⟶ x = y) ⟶ P (SUCH 'a P).

begin

instance Prop.UniqueSuchTyped;
	note#cong eq_cong_meta.
	- for x if Px: P.[x], uniq: ∀y. P.[y] ⟹ y : 'a ⟹ x = y, ... then P.[such z : 'a. P.[z]];
		define f = (fun z : 'a. P.[z]).
		have fS: f (SUCH 'a f);
			apply unique_such_axiom[of 'a, THEN all_elim1[of f], THEN all_elim1[of x], THEN imp_elim1, THEN imp_elim1];
			by Px uniq #simp f_def.
		by fS[simp f_def] #simp such_def.
	.

---
Intentional conditional expression can be defined.
---
definition Prop_dest_ = (fun 'a : TYPE, t e : 'a, i : Prop.
	such r : 'a. (i ⟶ r = t) ∧ ((i ⟶ t = e) ⟶ r = e)
).

lemma Prop_dest__type: if ['a : TYPE] then Prop_dest_ 'a : 'a ⇒ 'a ⇒ Prop ⇒ 'a;
	simp Prop_dest__def.
note Prop_dest__type1: Prop_dest__type[THEN to_elim1].
note Prop_dest__type2: Prop_dest__type1[THEN to_elim1].
note Prop_dest__type3: Prop_dest__type2[THEN to_elim1].

definition Prop_dest = (IMPLICIT 'a : TYPE. 'a) Prop_dest_.

lemma Prop_dest: for 'a
	if [t : 'a, 'a : TYPE] then Prop_dest t = Prop_dest_ 'a t;
	simp Prop_dest_def IMPLICIT[of 'a].

definition Prop_case = dual (dual ∘ Prop_dest).

extend Truth begin

	definition Truth_dest_ =
		(fun 'a : TYPE, t e : 'a, b : Truth. Prop_dest_ 'a t e (is_true b)).

	lemma Truth_dest__type: if ['a : TYPE] then Truth_dest_ 'a : 'a ⇒ 'a ⇒ Truth ⇒ 'a;
		simp Truth_dest__def; by Prop_dest__type3.
	note Truth_dest__type1: Truth_dest__type[THEN to_elim1].
	note Truth_dest__type2: Truth_dest__type1[THEN to_elim1].
	note Truth_dest__type3: Truth_dest__type2[THEN to_elim1].

	definition Truth_dest = (IMPLICIT 'a : TYPE. 'a) Truth_dest_.

	lemma Truth_dest: for 'a
		if [t : 'a, 'a : TYPE] then Truth_dest t = Truth_dest_ 'a t;
		simp Truth_dest_def IMPLICIT[of 'a].

	definition Truth_case = dual (dual ∘ Truth_dest).

	definition (if) = id.
	definition (then) = (|>) ∘ truth_of.
	definition (else) = Truth_dest.

	lemma if_then_else: (if i then t else e) = Truth_dest t e (truth_of i);
		unfold if_def then_def else_def; .

	instance IfTyped;
		- for 'a; by Truth_dest__type3 #simp if_then_else Truth_dest[of 'a].
		- for 'a if i: i, [i : Prop, 'a : TYPE, t : 'a, e : 'a] then (if i then t else e) = t;
			note! eq_prop[of 'a, OF !].
			note#simp i[THEN truth_of_eq_True].
			simp if_then_else Truth_dest[of 'a] Truth_dest__def Prop_dest__def;
			apply such_eq_intro;
			- .
			- for r if r, ... then t = r;
				apply r[THEN and_elim];
				- if t, e; apply eq.sym, t[THEN imp_elim1].
				.
			.
		- for 'a if i0: i ⟹ t = e, [i : Prop, 'a : TYPE, t : 'a, e : 'a] then (if i then t else e) = e;
			note! eq_prop[of 'a, OF !].
			simp if_then_else Truth_dest[of 'a] Truth_dest__def Prop_dest__def;
			apply such_eq_intro;
			- by i0[dual] #elim is_true_truth_of_elim1.
			- for r if r, ... then e = r;
				apply r[THEN and_elim];
				- if t, e; apply eq.sym, e[THEN imp_elim1];
					unfold[on (⟷)] is_true_truth_of_iff;
					by i0.
				.
			.
		.

	instance IfTyped.IntuitionisticNot.

	lemma if_cong: for 'a
		if P: P ⟷ P', t: t = t', e: e = e', [P : Prop, P' : Prop, t : 'a, t' : 'a, e : 'a, e' : 'a, 'a : TYPE]
		then (if P then t else e) = (if P' then t' else e');
		note#cong truth_of_cong.
		simp if_then_else P t e.

	instance Typedef;
		- for ARG Rep pred witness
			if Rep_type!, pred_type, witness_type!, witness for thesis if assm then thesis;
			define prj = (fun 'X : ARG, x : Rep.['X]. if pred 'X x then x else witness 'X).
			interpret QuotientType ARG Rep (fun 'X : ARG. rel_image (prj 'X) (fun x y : Rep.['X]. x = y));
				have prjX_type: for 'X if X! 'X : ARG then prj 'X : Rep.['X] ⇒ Rep.['X];
					simp prj_def; by pred_type[OF X, THEN to_elim1].
				- .
				- if X! 'X : ARG; simp;
					by rel_image_type2[OF prjX_type[OF X]] eq_prop[of Rep.['X]].
				- if X! 'X : ARG;
					interpret equivalence Rep.['X] (fun x y : Rep.['X]. x = y);
						by eq_equivalence.
					by image_equivalence[OF prjX_type[OF X]].
				.
			apply assm[of Abs abs_ rep_ ];
				- apply Abs_type.
				- apply abs__type=.
				- apply rep__type=.
				- if ['X : ARG, a : Abs 'X] then pred 'X (rep_ 'X a);
					have: prj 'X (rep_ 'X a) = prj 'X (rep_ 'X a);


end