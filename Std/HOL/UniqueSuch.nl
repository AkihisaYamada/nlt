---
# Unique Choice Operator
---

import SuchSignature.
assume unique_such_axiom: if 'a : TYPE then
	∀P : 'a → Prop. ∀x : 'a. P x ⟶ (∀y : 'a. P y ⟶ x = y) ⟶ P (SUCH 'a P).

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

definition cond_ = (fun 'a : TYPE, t e : 'a, i : Prop.
	such r : 'a. (i ⟶ r = t) ∧ ((i ⟶ t = e) ⟶ r = e)
).

lemma cond__type: if ['a : TYPE] then cond_ 'a : 'a → 'a → Prop → 'a;
	simp cond__def.
note cond__type1: cond__type[THEN to_elim1].
note cond__type2: cond__type1[THEN to_elim1].
note cond__type3: cond__type2[THEN to_elim1].

definition (if) = (_implicit 'a : TYPE. 'a) (fun 'a : TYPE, r : 'a. r).
definition (then) = (fun i : Prop. (_implicit 'a : TYPE. Prop → 'a) (fun 'a : TYPE, c : Prop → 'a. c i)).
definition (else) = (_implicit 'a : TYPE. 'a) cond_.

lemma if_then_else_ :
	if ['a : TYPE, i : Prop, t : 'a, e : 'a]
	then (if i then t else e) = cond_ 'a t e i;
	note! cond__type2 cond__type3.
	.. = (if i then cond_ 'a t e);
		apply arg_cong, arg_cong;
		simp else_def _implicit[of 'a].
	.. = (if cond_ 'a t e i);
		apply arg_cong;
		simp then_def _implicit[of 'a].
	simp if_def _implicit[of 'a].

instance IfTyped;
	- for 'a; by cond__type3 #simp if_then_else_[of 'a].
	- for 'a if i: i, [i : Prop, 'a : TYPE, t : 'a, e : 'a] then (if i then t else e) = t;
		note! eq_prop[of 'a, OF !].
		simp if_then_else_[of 'a] cond__def;
		apply such_eq_intro;
		- simp[on (⟷)] i[THEN iff_true].
		- for r if r, ... then t = r;
			apply r[THEN and_elim];
			- if t, e; apply eq.sym, t[THEN imp_elim1], i.
			.
		.
	- for 'a if i0: i ⟹ t = e, [i : Prop, 'a : TYPE, t : 'a, e : 'a] then (if i then t else e) = e;
		note! eq_prop[of 'a, OF !].
		simp if_then_else_[of 'a] cond__def;
		apply such_eq_intro;
		- by i0[dual].
		- for r if r, ... then e = r;
			apply r[THEN and_elim];
			- if t, e; apply eq.sym, e[THEN imp_elim1], imp_intro[OF i0].
			.
		.
	.

instance IfTyped.IntuitionisticNot.
