---
# Equational Logic

With type-free equality, equations are not necessarily propositions.
---
import ..Prop.
fix EQTYPE.
assume eq_prop(intro 1) if A ∈ EQTYPE then ∀x. x ∈ A ⟹ ∀y. y ∈ A ⟹ x = y ∈ Prop.

begin

interpret .Classes.

theory Pair:
	import Pair.
	assume prod_type(intro) if A ∈ EQTYPE, B ∈ EQTYPE then A × B ∈ EQTYPE.
begin
	lemma pair_eq_prop:
		if [A ∈ EQTYPE, B ∈ EQTYPE, x ∈ A, y ∈ B, x' ∈ A, y' ∈ B]
		then (x,y) = (x',y') ∈ Prop;
	by eq_prop[of (A×B)].

end


theory Minimal:
	import Minimal.
begin

	set rewrite! iff.imp iff.imp_rev iff.refl iff.trans.
	set dual iff.sym.

	lemma eq_imp_iff(cong) if eq: P = P', !P ∈ Prop then P ⟺ P';
		have !P' ∈ Prop;
			by #fold(=) eq.
	by iff_intro #unfold(=) eq.

	theory If:
		fix (if) (then) (else).
		assume if_then: if P, P ∈ Prop then (if P then x else y) = x.
		assume if_else: if ¬P, P ∈ Prop then (if P then x else y) = y.
	begin

	end

	theory Pair:
		import Pair.
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
				have (unfold) x = x';
					apply and.elim[OF and].
				have (unfold) y = y';
					apply and.elim[OF and].
			by pair_eq_prop[OF A B].
		by pair_eq_prop[OF A B].
	end

end

theory Intuitionistic:
	import Intuitionistic.
begin
	interpret Minimal.
end

theory Classical:
	import Classical.
begin
	interpret Intuitionistic.
end
