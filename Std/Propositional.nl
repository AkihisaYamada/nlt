---
# Propositions

We fix a class `Prop` in which logical operators are closed.
---
import Membership.

fix Prop.
import imp: Magma Prop (⟹).

begin

note! imp.closed.

theory Relation A (⊏) :=
	import Binary (⊏) A A Prop.
end

theory PierceLaw :=
	assume pierce_law: if (P ⟹ Q) ⟹ P, P ∈ Prop, Q ∈ Prop then P.
end

theory True :=
	fix true.
	assume true_prop! true ∈ Prop.
	assume true_intro! true.
end

theory False :=
	fix false.
	assume false_prop! false ∈ Prop.
	assume false_elim: if false, P ∈ Prop then P.
begin

	interpretation True;
		obtain true where true_def: if P.[false ⟹ false] then P.[true];
			- for thesis if assm;
				apply assm[of (false ⟹ false)].
			.
		- apply true_def[of (x. x ∈ Prop)].
		- apply true_def[of (x. x)].
		.

end
