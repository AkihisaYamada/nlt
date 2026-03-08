---
# Theory of Classes

The Morse--Kelley set theory (MK) is an extension of the von Neumann--Bernays--Gödel set theory (NBG)
where comprehension w.r.t. formulas mentioning classes are allowed.
Being a set is defined as being a member of a class.
In type theory, being a member of a type is crucial.
In this theory, we call members of classes objects.
We further allow comprehension w.r.t. non-formulas.
---
import Eq.
import TypeFree.
import Minimal.
import Membership.
import AllIn.
import ExIn.
import Ex1In.
import Pair.
import UniqueChoice.

fix Class.
assume Class_eq_intro: if ∀x. x ∈ A ⟺ x ∈ B, A ∈ Class, B ∈ Class then A = B.

fix Object.
assume Object_Class: Object ∈ Class.
assume Object_iff: x ∈ Object ⟺ (∃A ∈ Class. x ∈ A).

lemma in_Class_imp_Object: if A: A ∈ Class, x: x ∈ A then x ∈ Object;
	unfold Object_iff;
	apply in.ex_intro1[OF A];
	by x.

assume comprehension_schema: ∀P. ∃A ∈ Class. ∀x ∈ Object. x ∈ A ⟺ P.[x].

lemma comprehension_strong: for P then ∃A ∈ Class. ∀x. x ∈ A ⟺ x ∈ Object ∧ P.[x];
	apply comprehension_schema[of P, THEN in.ex_elim];
	- for A if Aty, A1;
		apply in.ex_intro1[OF Aty];
		- for x then x ∈ A ⟺ x ∈ Object ∧ P.[x];
			apply iff_intro;
			- if xA;
				note xO: in_Class_imp_Object[OF Aty xA].
				by xO xA[unfold A1[rule, OF xO]].
			simp A1[rule].
		.
	.

lemma comprehension_ex1: for P then ∃!A ∈ Class. ∀x. x ∈ A ⟺ x ∈ Object ∧ P.[x];
	apply comprehension_strong[of P, THEN in.ex_elim];
	- for A if Aty!, A;
		apply in.ex1_intro1[of A];
		- by A.
		- by Aty.
		- for B if Bty!, B;
			apply Class_eq_intro;
			simp A B;
			.
		.
	.

syntax {_. _} := Collect.
obtain Collect where
	Collect_Class! {x. P.[x]} ∈ Class,
	Collect_iff: x ∈ {x. P.[x]} ⟺ x ∈ Object ∧ P.[x];
	- for thesis if assm;
		apply unique_choice[of Class (p. ∃P A. p = (P,A) ∧ (∀x. x ∈ A ⟺ x ∈ Object ∧ P.[x])), THEN ex_elim];
		- for P;
			apply imp_commute[OF in.ex1_cong[of Class, OF eq.refl, THEN iff_elim1], OF comprehension_ex1, of P];
			- for A if Aty!;
				apply iff_intro;
				- if Aiff;
					apply ex_intro1[of P];
					apply ex_intro1[of A];
					simp Aiff.
				simp;
				- for P' A' if PP', (simp), (simp);
					simp eq_cong_meta[for x, of (P. P.[x]), OF PP'].
				.
			.
		- for _Collect if C;
			apply assm[of _Collect];
			- for P;
				use C[of (x. P.[x])].
			- for x P;
				use C[of (x. P.[x])];
				simp;
			 	- if ty for P' C' if P', C', iff;
					simp iff[fold C' P'] eq_cong_meta[for z, of (P. P.[z]), OF P'].
				.
			.
		.
	.

lemma Collect_cong(cong)
	if PQ: ∀x. x ∈ Object ⟹ P.[x] ⟺ Q.[x] then {x. P.[x]} = {x. Q.[x]};
	apply Class_eq_intro;
	by #simp Collect_iff PQ.

syntax {} := empty.
define {} = {x. false}.

lemma empty_Class! {} ∈ Class;
	unfold empty_def.

lemma not_in_empty: ¬x ∈ {};
	by nand_false #simp empty_def Collect_iff.

syntax {_} := singleton.
obtain singleton where singleton_def: {a} = {x. a = x};
	apply abbrev[of Class]>1=.

lemma singleton_iff(simp) x ∈ Object ⟹ x ∈ {a} ⟺ x = a;
	by iff_eq.commute #simp singleton_def Collect_iff.

obtain (⋃) where CUP_def: ⋃XX = {x. ∃X ∈ XX. x ∈ X};
	apply abbrev[of Class]>1=.

lemma CUP_Class! ⋃XX ∈ Class;
	unfold CUP_def.

lemma CUP_iff: x ∈ Object ⟹ x ∈ ⋃XX ⟺ (∃X ∈ XX. x ∈ X);
	simp CUP_def Collect_iff.

obtain (⋂) where CAP_def: ⋂XX = {x. ∀X ∈ XX. x ∈ X};
	apply abbrev[of Class]>1=.

lemma CAP_Class! ⋂XX ∈ Class;
	unfold CAP_def.

lemma CAP_iff: x ∈ Object ⟹ x ∈ ⋂XX ⟺ (∀X ∈ XX. x ∈ X);
	simp CAP_def Collect_iff.

fix (×).
assume pair_in_prod_iff: (x,y) ∈ A × B ⟺ x ∈ A ∧ y ∈ B.
assume prod_Class: if A ∈ Class, B ∈ Class then A × B ∈ Class.

infix ∪(,) 71 70 71.
obtain (∪) where cup_def: A ∪ B = {x. x ∈ A ∨ x ∈ B};
	- for thesis if assm;
		apply abbrev[of Class ((A,B). {x. x ∈ A ∨ x ∈ B})];	
		-.
		- for (∪) if cup_def;
			apply assm[of (∪)];
			simp cup_def;.
		.
	.

lemma cup_Class! A ∪ B ∈ Class;
	unfold cup_def.

lemma cup_iff: x ∈ Object ⟹ x ∈ A ∪ B ⟺ x ∈ A ∨ x ∈ B;
	simp cup_def Collect_iff.

infix ∩(,) 81 80 81.
obtain (∩) where cap_def: A ∩ B = {x. x ∈ A ∧ x ∈ B};
	- for thesis if assm;
		apply abbrev[of Class ((A,B). {x. x ∈ A ∧ x ∈ B})];
		-.
		- for (∩) if cap_def;
			apply assm[of (∩)];
			simp cap_def.
		.
	.

syntax {_ ∈ _. _} := CollectIn.
obtain CollectIn where
	CollectIn_Class! if A ∈ Class then {x ∈ A. P.[x]} ∈ Class,
	CollectIn_iff: if A ∈ Class then x ∈ {x ∈ A. P.[x]} ⟺ x ∈ A ∧ P.[x];
	- for thesis if assm;
		apply assm[of (λ(A,P). _Collect 

theory Minimal:
	import Minimal.
	fix {}.
begin

end

theory Intuitionistic:
	import Intuitionistic.
begin
	interpret _.Minimal;
			.
		.

end
