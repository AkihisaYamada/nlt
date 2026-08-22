---
# HOL Set

Sets are encoded as predicates, but to ensure extensionality of sets, it is necessary that predicates are extensional, and propositions are identified by `⟺`.
---
import Typedef, IfTyped, Ext.

begin

instance Set: TypeDefinition TYPE ('a. 'a → Prop) is_set_ ;
	- by is_set__type.
	- for thesis if assm then thesis;
		apply assm[of (fun 'a : TYPE, x : 'a. false)]; by #simp is_set__def.
	.

definition Set = Set.Abs.

definition[as _in] (∈) =
	(_implicit 'a : TYPE. 'a) (fun 'a : TYPE, x : 'a, A : Set 'a. Set.rep A x).

lemma in_def: if ['a : TYPE, x : 'a, A : Set 'a] then (x ∈ A) = Set.rep A x;
	simp _in_def _implicit[of 'a].

lemma in_type! if ['a : TYPE, x : 'a, A : Set 'a] then x ∈ A : Prop;
	by #simp in_def[of 'a] Set_def[dual] #intro Set.rep_type[of 'a, THEN to_elim1].

definition make_bool = (fun p : Prop. if p then true else false).

lemma make_bool_type! make_bool : Prop → Prop; by #simp make_bool_def #intro if_type[of Prop].

definition (Collect_:) =
	(fun 'a : TYPE. Set.abs ∘ (make_bool ∘) ∘ (fun_:) 'a).

lemma Collect_type: if ['a : TYPE, ∀

lemma in_Collect_intro:
	if Px: P.[x], ['a : TYPE, x : 'a, ∀x. x : 'a ⟹ P.[x] : Prop]
	then x ∈ {x : 'a. P.[x]};
	simp Collect_:_def _implicit[of 'a]; 

lemma IN_Collect#simp
	if ['a : TYPE, x : 'a, ∀y. y : 'a ⟹ F.[y] : Bool]
	then IN 'a x {x : 'a. F.[x]} = F.[x];
	simp Collect_eq IN_Set_Abs.

lemma set_eq_intro:
	if eq: ∀x. x : 'a ⟹ IN 'a x X = IN 'a x X', ['a : TYPE, X : Set 'a, X' : Set 'a]
	then X = X';
	.. = Set.Abs 'a (Set.Rep 'a X);
		apply Set.Abs_Rep[dual]; by #simp Set_def[dual].
	.. = Set.Abs 'a (Set.Rep 'a X');
		apply arg_cong;
		apply ext[of 'a Bool];
		- if [x : 'a];
			fold IN_eq_Set_Rep; apply eq.
		by Set.Rep_type1 #simp Set_def[dual].
	apply Set.Abs_Rep; by #simp Set_def[dual].

definition EMPTY = fun 'a : TYPE. {x : 'a. bool false}.

lemma IN_EMPTY: if ['a : TYPE, x : 'a] then IN 'a x (EMPTY 'a) = bool false;
	simp EMPTY_def.

definition SINGLETON = fun 'a : TYPE, x : 'a. {y : 'a. bool (x = y)}.

lemma IN_SINGLETON:
	if ['a : TYPE, x : 'a, y : 'a]
	then IN 'a x (SINGLETON 'a y) = bool (y = x);
	simp SINGLETON_def.

definition CUP = fun 'a : TYPE, X : Set 'a, Y : Set 'a. {x : 'a. IN 'a x X || IN 'a x Y}.

lemma IN_CUP: if ['a : TYPE, x : 'a, X : Set 'a, Y : Set 'a]
	then IN 'a x (CUP 'a X Y) = (IN 'a x X || IN 'a x Y);
	simp CUP_def.

definition CAP = fun 'a : TYPE, X : Set 'a, Y : Set 'a. {x : 'a. IN 'a x X && IN 'a x Y}.

lemma IN_CAP: if ['a : TYPE, x : 'a, X : Set 'a, Y : Set 'a]
	then IN 'a x (CAP 'a X Y) = (IN 'a x X && IN 'a x Y);
	simp CAP_def.
