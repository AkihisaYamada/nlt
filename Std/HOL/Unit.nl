import Typedef.

begin

instance Unit: TypeDefinition TYPE (x. Prop) (fun _ : TYPE, x : Prop. x = true);
	- .
	- for thesis;
		- if assm; apply assm[of (fun _ : TYPE. true)].
		.
	.

definition Unit = Unit.Abs Prop.

definition unit = Unit.abs true.

lemma unit_type! unit : Unit;
	unfold Unit_def unit_def;
	apply Unit.abs_type.

lemma Unit_eq_unit: if a: a : Unit then a = unit;
	note a0! a[unfold Unit_def].
	note! Unit.rep_type[of Prop, OF ! ].
	.. = Unit.abs (Unit.rep a);
		apply eq.sym, Unit.abs_rep[of Prop, OF !].
	.. = Unit.abs true;
		apply arg_cong, Unit.rep[of Prop, OF ! a0, simp].
	unfold unit_def.
