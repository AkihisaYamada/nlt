---
# Theory of Classes

The Morse--Kelley set theory (MK) is an extension of the von Neumann--Bernays--Gödel set theory (NBG)
where comprehension w.r.t. formulas mentioning classes are allowed.
Being a set is defined as being a member of a class.
In type theory, being a member of a type is crucial.
In this theory, we call members of classes objects.
We further allow comprehension w.r.t. non-formulas.
---
fix class.

import Eq.
import TypeFree.
import Minimal.
import Membership.
import AllIn.
import ExIn.
import Ex1In.

---
Classes are identified by their memberships.
---
assume class_ext: if class X, class Y, ∀x. x ∈ X ⟺ x ∈ Y then X = Y.

syntax {} := empty.
syntax {_} := singleton.
infix ∪(,) 71 70 71.
infix ∩(,) 81 80 81.
infix ×(,) 111 110 110.
infix `(,) 101 100 100.
syntax {_ ∈ _. _} := CollectIn(,).

begin

lemma class_eq_intro: if iff: ∀x. x ∈ X ⟺ x ∈ Y, X: class X, Y: class Y then X = Y;
	apply class_ext[OF X Y iff].

theory CollectIn:
	fix CollectIn.
	assume CollectIn_class! if class A then class {x ∈ A. P.[x]}.
	assume CollectIn_iff: if class A then x ∈ {x ∈ A. P.[x]} ⟺ x ∈ A ∧ P.[x].
begin

	lemma CollectIn_cong#cong
		if A: class A, AB: A = B, PQ: ∀x. x ∈ B ⟹ P.[x] ⟺ Q.[x]
		then {x ∈ A. P.[x]} = {x ∈ B. Q.[x]};
		apply class_eq_intro;
		by #simp CollectIn_iff AB PQ #intro A[simp].

	lemma CollectIn_true: if A: class A then {x ∈ A. true} = A;
		apply class_eq_intro;
		by A #simp CollectIn_iff.

end

theory ComprehensionSchema:
	assume comprehension_schema: for A P if class A then ∃X. class X ∧ (∀x. x ∈ X ⟺ x ∈ A ∧ P.[x]).
begin
	lemma comprehension_ex1: for A P if A: class A then ∃!X. class X ∧ (∀x. x ∈ X ⟺ x ∈ A ∧ P.[x]);
		apply comprehension_schema[of A P, OF A, THEN ex_elim];
		-> for X if Xty!, X;
			apply ex1_intro1[of X];
			- by #simp X.
			-> for Y if Yty!, Y;
				apply class_eq_intro;
				simp X Y.
			.
		.
end

extend UniqueChoiceCond begin

	extend ComprehensionSchema begin

		interpret CollectIn;
			obtain CollectIn where
				CollectIn_class! if class A then class {x ∈ A. P.[x]},
				CollectIn_iff: if class A then x ∈ {x ∈ A. P.[x]} ⟺ x ∈ A ∧ P.[x];
				- for thesis if assm;
					apply unique_choice_cond[of
						(p. ∃A P. p = (A, x. P.[x]))
						((A,P). Pow A)
						(t. ∃A P B. t = ((A, x. P.[x]), B) ∧ (∀x. x ∈ B ⟺ x ∈ A ∧ P.[x])), THEN ex_elim];
					simp;
					- for p A P if p;
						apply ex1_cong[OF eq.refl, THEN imp_commute[OF iff_elim1][OF comprehension_ex1], of A (x. P.[x])];
						- for X if Xty!;
							apply iff_intro;
							- if Xiff;
								apply ex_intro1[of A];
								apply ex_intro1[of P];
								simp Xiff p ex_eq_and_iff2.
							simp p;
							- for A' P' X' if (simp), PP', (simp);
								simp eq_cong_meta[for x, of (P. P.[x]), OF PP'].
							.
						.
					- for CollectIn if C;
						note C2: C[OF eq.refl].
						apply assm[of CollectIn];
						- for A P;
							use C2[of A P];.
						- for x A P;
							use C2[of A P];
							simp;
						 	- if ty for A' P' C' if A', P', C', iff;
								simp iff[fold A' C'] eq_cong_meta[for z, of (P. P.[z]), OF P'].
							.
						.
					.
				.
			.
	end

end

theory PowerClass:
	fix Pow.
	assume Pow_class: if class A then class (Pow A).
	assume Pow_iff: if class A then X ∈ Pow A ⟺ class X ∧ (∀x. x ∈ X ⟹ x ∈ A).
end

theory MK:
	fix Object.
	assume Object_class! class Object.
	import CollectIn.
begin
	define


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
