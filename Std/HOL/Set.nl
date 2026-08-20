---
# HOL Set

Sets are encoded as predicates, but to ensure extensionality of sets, it is necessary that predicates are extensional, and propositions are two valued.
---
import Typedef, Ext, Bool.

begin

instance Set: TypeDefinition TYPE ('a. 'a → Bool) (fun 'a : TYPE, f : 'a → Bool. true);
	- for thesis if assm then thesis;
		apply assm[of (fun 'a : TYPE, x : 'a. bool false)].
	.

definition Set = Set.ABS.

definition IN = fun 'a : TYPE, x : 'a, A : Set 'a. Trueprop (Set.Rep 'a A x).

lemma IN_type: if ['a : TYPE] then IN 'a : 'a → Set 'a → Prop;
	by #simp IN_def Set_def[dual] #intro Set.Rep_type1[THEN to_elim1].

lemma IN_eq_Set_Rep: if ['a : TYPE, x : 'a, A : Set 'a] then IN 'a x A = Trueprop (Set.Rep 'a A x);
	simp IN_def.

lemma IN_Set_Abs:
	if 'a! 'a : TYPE, [x : 'a], f! f : 'a → Bool
	then IN 'a x (Set.Abs 'a f) = Trueprop (f x);
	by Set.Abs_type[OF 'a, THEN to_elim1, OF f] #simp IN_def Set.Rep_Abs[OF 'a f, simp] Set_def.

definition Collect_: = _BINDER Set.Abs.

lemma Collect_eq: {x : 'a. F.[x]} = Set.Abs 'a (fun x : 'a. F.[x]);
	simp Collect_:_def.

lemma IN_Collect#simp
	if ['a : TYPE, x : 'a, ∀y. y : 'a ⟹ F.[y] : Bool]
	then IN 'a x {x : 'a. F.[x]} = Trueprop F.[x];
	simp Collect_eq IN_Set_Abs.

lemma set_eq_intro:
	if iff: ∀x. x : 'a ⟹ IN 'a x X ⟷ IN 'a x X', ['a : TYPE, X : Set 'a, X' : Set 'a]
	then X = X';
	have 1: Set.Rep 'a X = Set.Rep 'a X';
		apply ext[of 'a Prop];
		- if [x : 'a];
			fold IN_eq_Set_Rep; thm iff.

	.. = Set.Abs 'a (Set.Rep 'a X);
		apply Set.Abs_Rep[dual]; by #simp Set_def[dual].
	.. = 


definition EMPTY = fun 'a : TYPE. {x : 'a. false}.



