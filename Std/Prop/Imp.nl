fix (⟶).
assume imp_type! (⟶) : Prop → Prop → Prop.
assume imp_intro! if P ⟹ Q, P : Prop, Q : Prop then P ⟶ Q.
assume imp_elim1: if P ⟶ Q, P, P : Prop, Q : Prop then Q.

import False.

begin

note imp_type1! imp_type[THEN to_elim1].
note imp_type2! imp_type1[THEN to_elim1].

instance True;
	obtain true where true_prop! true : Prop, true_intro! true;
		- for thesis if assm;
			apply assm[of (false ⟶ false)].
		.
	.

lemma imp_elim: if PQ: P ⟶ Q, [P : Prop, Q : Prop], assm: (P ⟹ Q) ⟹ R then R;
	apply assm; by imp_elim1[OF PQ].

instance IMP: Magma Prop (⟶).
note! IMP.closed.

instance imp_IMP: imp.LeftMonotone Prop Prop (⟶);
	- if y: y ⟹ y', [x : Prop, y : Prop, y': Prop], xy: x ⟶ y then x ⟶ y';
		by imp_intro xy[THEN imp_elim1] y.
	.

instance IMP: Preorder Prop (⟶);
	- if [x : Prop] then x ⟶ x; by imp_intro.
	- if xy: x ⟶ y, yz: y ⟶ z, ... then x ⟶ z;
		by imp_intro yz[THEN imp_elim1] xy[THEN imp_elim1].
	.

note#refl IMP.refl.
note#trans IMP.trans.

instance IMP: Magmas (⟶) (:).



lemma imp_elim_rule#elim[guards 2] if PQ: P ⟶ Q, [P : Prop, Q : Prop], P: P then Q;
	by imp_elim1[OF PQ P].

theory PeirceLaw :=
	assume peirce_law: for Q if (P ⟶ Q) ⟶ P, P : Prop, Q : Prop then P.
end

