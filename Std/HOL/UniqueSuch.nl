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
