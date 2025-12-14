---
# Type-Free Equality and Propositions

With type-free equality, equations are not necessarily propositions.
It is assumed equations over terms of a type of class `EQTYPE` are propositions.
---
fix (∈) PROP EQTYPE.

set print.

import ..Prop.

assume eq_prop? ? if A ∈ EQTYPE then ∀x. x ∈ A ⟹ ∀y. y ∈ A ⟹ x = y ∈ PROP.

begin

interpret .Classes.
set print blast.
interpret weak_eq: Prop.Eq;
	-.
	for P A x y if !, eq, Px;
		by eq_imp_meta[of P, OF eq Px].
	.

theory Minimal:
	import Prop.Minimal.
begin
	theory If:
		fix (if) (then) (else).
		assume if_then:
			if A ∈ EQTYPE, B ∈ EQTYPE, P, P ∈ PROP, x ∈ A, y ∈ B
			then (if P then x else y) = x.
		assume if_else:
			if A ∈ EQTYPE, B ∈ EQTYPE, P, P ∈ PROP, x ∈ A, y ∈ B
			then (if ¬P then x else y) = y.
	begin

	end

	theory Prod:
		import Prod.
		-- Products of `EQTYPE` are `EQTYPE`.
		assume prod_type! if A ∈ EQTYPE, B ∈ EQTYPE then A × B ∈ EQTYPE.
	begin
		lemma pair_eq_iff:
			if A! A ∈ EQTYPE, B! B ∈ EQTYPE, [x ∈ A, y ∈ B, x' ∈ A, y' ∈ B]
			then (x,y) = (x',y') ⟺ x = x' ∧ y = y';
			apply iff_intro;
			if eq;
				apply and_intro;
				- by pair_eq_pair_imp1[OF eq].
				- by pair_eq_pair_imp2[OF eq].
				.
			if and;
				have #unfold: x = x';
					apply and.elim[OF and];
					.
				have #unfold: y = y';
					apply and.elim[OF and];
					.
				.
			apply eq_prop[OF prod_type[OF A B]];
			.
	end
end

theory Intuitionistic:
	import ..Intuitionistic.
begin
	interpret Minimal.
end

theory Classical:
	import ..Classical.
begin
	interpret Intuitionistic.
end
