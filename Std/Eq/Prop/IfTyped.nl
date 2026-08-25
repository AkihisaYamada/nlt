
fix (if) (then) (else).
assume if_type! for 'a
	if P : Prop, 'a : EQTYPE, t : 'a, e : 'a then (if P then t else e) : 'a.
assume if_then: for 'a
	if P, P : Prop, 'a : EQTYPE, t : 'a, e : 'a then (if P then t else e) = t.
assume if_else_weak: for 'a
	if P ⟹ t = e, P : Prop, 'a : EQTYPE, t : 'a, e : 'a then (if P then t else e) = e.

import True, False.

begin

lemma if_true: for 'a if ['a : EQTYPE, t : 'a, e : 'a] then (if true then t else e) = t;
	apply if_then[of 'a].

lemma if_false: for 'a if ['a : EQTYPE, t : 'a, e : 'a] then (if false then t else e) = e;
	apply if_else_weak[of 'a]; by #elim false_elim.

extend IntuitionisticNot begin

	lemma if_not: for 'a
		if nP: ¬P, [P : Prop, 'a : EQTYPE, t : 'a, e : 'a] then (if P then t else e) = e;
		apply if_else_weak[of 'a];
		- if P; apply not_elim[OF nP P].
		.

end