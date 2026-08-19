fix Prop.

assume Subtype: for 'a pred witness if
	pred witness,
	∀Type.
		Type : TYPE ⟹
		(∀x. x : Type ⟹ pred x) ⟹
		(∀x. x : Type ⟹ x : 'a) ⟹
		(∀x. x : 'a ⟹ pred x ⟹ x : Type) ⟹ thesis,
	'a : TYPE,
	witness : 'a
	then thesis.

begin

theory Subtype 'a pred :=
	assume witness: if ∀witness. pred witness ⟹ witness : 'a ⟹ thesis then thesis.
	assume base_type! 'a : TYPE.
	assume pred_type: pred : 'a → Prop.
begin
	obtain Type where
		Type_TYPE: Type : TYPE,
		elim0: if x : Type then x : 'a,
		elim1: if x : Type then pred x,
		intro: if x : 'a, pred x then x : Type;
	- for thesis if assm;
		apply witness;
		- if witness: pred witness, ...;
			apply Subtype[of 'a, OF witness];
			- for Type if ...;
				apply assm[of Type].
			.
		.
	.

end
