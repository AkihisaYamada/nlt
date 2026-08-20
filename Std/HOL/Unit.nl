import Typedef.

begin

instance Unit: TypeDefinition TYPE (x. Prop) (fun _ : TYPE, x : Prop. x = true);
	- .
	- for thesis;
		- if assm; apply assm[of (fun _ : TYPE. true)].
		.
	.

definition Unit = Unit.ABS Prop.

definition unit = Unit.Abs Prop true.

lemma unit_type! unit : Unit;
	unfold Unit_def unit_def;
	apply Unit.Abs_type1.

lemma Unit_eq_unit: if a: a : Unit then a = unit;
	note! a[unfold Unit_def].
	note! Unit.Rep_type1[of Prop, OF ! ].
	.. = Unit.Abs Prop (Unit.Rep Prop a);
		apply eq.sym, Unit.Abs_Rep[of Prop, OF !].
	have 1: Unit.Rep Prop a = true; apply Unit.Rep[OF a[unfold Unit_def], OF !, simp].
	unfold 1, unit_def.
