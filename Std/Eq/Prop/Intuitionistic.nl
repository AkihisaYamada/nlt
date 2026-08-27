import Std_Prop.Intuitionistic, Comp.

begin

instance .Minimal.

lemma neq_imp_false: for 'a
	if neq: x ≠ y, eq: x = y, [x : 'a, y : 'a, 'a : EQTYPE] then false;
	apply not_imp_false[OF neq[unfold neq_eq] eq].
