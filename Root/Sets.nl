---
# Basis for Set Theories 
---
fix Set.
import Eq.
import TypeFree.
import Minimal.
import Membership.
import AllIn.
import ExIn.
import Ex1In.
import Pair.

syntax {} := empty.
syntax {_} := singleton.
infix ∪(,) 71 70 71.
infix ∩(,) 81 80 81.
infix ×(,) 111 110 110.
infix `(,) 101 100 100.
syntax {_ ∈ _. _} := CollectIn(,).

---
## Axiomatization

Members of sets are sets.
---
assume in_set_imp_set: if A ∈ Set, x ∈ A then x ∈ Set.

---
### Extensionality

Extensionality asserts that sets `A` and `B` are equal if `x ∈ A ⟺ x ∈ B` for any `x`.
Strictly speaking, ZF variables range over sets, so this axiom would be formalized to
`∀A ∈ Set. ∀B ∈ Set. (∀x ∈ Set. x ∈ A ⟺ x ∈ B) ⟹ A = B`
but restricting `x` to `Set` here is useless.
---
assume extensionality_axiom: ∀A ∈ Set. ∀B ∈ Set. (∀x ∈ Set. x ∈ A ⟺ x ∈ B) ⟹ A = B.

begin

---
As an inference rule:
---
lemma set_eq_intro: if eq: ∀x. x ∈ Set ⟹ x ∈ A ⟺ x ∈ B, A! A ∈ Set, B! B ∈ Set then A = B;
	by extensionality_axiom[rule, OF A B] eq.

---
## Theories

### Empty Set
---
theory EmptySet:
	fix empty.
	assume empty_Set! {} ∈ Set.
	assume not_in_empty: ¬ x ∈ {}.
begin

	lemma in_empty_imp_false: if x0: x ∈ {} then false;
		by not_imp_false[OF not_in_empty x0].

end

theory EmptySetEx:
	assume ex_empty: ∃x ∈ Set. ¬(∃y ∈ Set. y ∈ x).
begin

	interpret EmptySet;
		obtain empty where empty_Set! {} ∈ Set, nexIn_empty: ¬(∃x ∈ Set. x ∈ {});
			- for thesis;
				apply in.ex_elim[OF ex_empty]>0.
			.
		-> if x0: x ∈ {};
			by nexIn_empty[rule, OF _ x0] in_set_imp_set[OF _ x0].
		.

end

context EmptySet begin

	interpret: EmptySetEx;
		- by in.ex_intro1[of {}] not_intro #elim in_empty_imp_false.
		retain empty;
			by not_intro #elim in_empty_imp_false.
		.

end

---
### Singleton Set
---
theory SingletonSet:
	fix singleton.
	assume singleton_Set! if x ∈ Set then {x} ∈ Set.
	assume singleton_iff: if x ∈ Set then y ∈ {x} ⟺ x = y.
end

---
### Unordered pairs
---

theory UnorderedPair:
	fix upair.
	assume upair_Set! if x ∈ Set, y ∈ Set then upair(x,y) ∈ Set.
	assume upair_iff: if x ∈ Set, y ∈ Set then z ∈ upair(x,y) ⟺ z = x ∨ z = y.
end
---
Abbreviation allows obtaining singleton `{x}` as the pair `{x,x}`.
---
extend AbbrevCond begin

	extend UnorderedPair begin
		interpret SingletonSet;
			obtain singleton where singleton_def: if x ∈ Set then {x} = upair(x,x);
				apply abbrev_cond[of (x. x ∈ Set) (x. Set)]>1=.
			- show! if ! x ∈ Set then {x} ∈ Set;
				unfold singleton_def.
			- if ! x ∈ Set then y ∈ {x} ⟺ x = y;
				unfold singleton_def upair_iff;
				by iff_eq.commute.
			.
	end

end

theory UnorderedPairEx:
	assume upair_axiom: ∀x ∈ Set. ∀y ∈ Set. ∃z ∈ Set. ∀w ∈ Set. w ∈ z ⟺ w = x ∨ w = y.
begin
	lemma ex1_upair: if x! x ∈ Set, y! y ∈ Set then ∃!z ∈ Set. ∀w ∈ Set. w ∈ z ⟺ w = x ∨ w = y;
		apply upair_axiom[rule, OF x y, THEN in.ex_elim];
		- for z if z! z ∈ Set, zall;
			apply in.ex1_intro1[of z];
			- by zall.
			- by z.
			- for z' if !, z'all;
				by set_eq_intro #simp z'all[rule] zall[rule].
			.
		.
end
---
Usual formulations of ZF then introduces a binary operator which,
given `x` and `y` as arguments, denotes the (unique) such `z`.
In Naive Logic, the assumption that one can do this must be explicitly formalized.
We do so by a unique choice axiom schema.
---
extend UniqueChoiceCond begin
	extend UnorderedPairEx begin
		interpret UnorderedPair;
			obtain upair where
				upair_Set! if x ∈ Set, y ∈ Set then upair(x,y) ∈ Set,
				upair_iff: if x ∈ Set, y ∈ Set then z ∈ upair(x,y) ⟺ z = x ∨ z = y;
				- for thesis if assm;
					apply unique_choice_cond[of
							(p. ∃x ∈ Set. ∃y ∈ Set. p = (x,y))
							(p. Set)
							(((x,y),z). ∀w ∈ Set. w ∈ z ⟺ w = x ∨ w = y),
						THEN ex_elim];
					simp;
					- by ex1_upair.
					- for f if f;
						apply assm[of f];
						- show set: if x: x ∈ Set, y: y ∈ Set; use f[OF x y eq.refl].
						- if x: x ∈ Set, y: y ∈ Set; use f[OF x y eq.refl] .
						.
					.
				.
			.
	end
end




---
### Separation Schema and Bounded Comprehension

The separation schema assumes for any set `A` and any predicate `P`,
the existence of the subset of `A` whose elements satisfy `P`.
On the other hand, bounded comprehension assumes the notation `{x ∈ A. P.[x]}` for this subset.
The latter trivially implies the former, while the converse holds under the unique choice schema.
---
theory CollectIn:
	fix CollectIn.
	assume CollectIn: for A P if A ∈ Set then {x ∈ A. P.[x]} ∈ Set.
	assume CollectIn_iff: for A P if A ∈ Set then x ∈ {x ∈ A. P.[x]} ⟺ x ∈ A ∧ P.[x].
end

theory SeparationSchema:
	assume separation_schema: ∀P. ∀A ∈ Set. ∃B ∈ Set. ∀x ∈ Set. x ∈ B ⟺ x ∈ A ∧ P.[x].
begin

	lemma separation_ex1:
		for P if A: A ∈ Set
		then ∃!B ∈ Set. ∀x ∈ Set. x ∈ B ⟺ x ∈ A ∧ P.[x];
		apply separation_schema[of P, rule, OF A, THEN in.ex_elim];
		- for B if B, Bspec;
			apply+ in.ex1_intro1[of B] in.all_intro B;
			- by Bspec[rule](simp).
			- for B' if B', B'spec;
				by set_eq_intro B B' #simp Bspec[rule] B'spec[rule].
			.
		.

	interpret CollectIn;
		obtain CollectIn where
			CollectIn: for A P if A ∈ Set then {x ∈ A. P.[x]} ∈ Set,
			CollectIn_iff: for A P if A ∈ Set then x ∈ {x ∈ A. P.[x]} ⟺ x ∈ A ∧ P.[x];
			- for thesis if assm;
				apply unique_choice_cond[
					of (p. ∃A P. p = (A, x. P.[x]) ∧ A ∈ Set)
					   (p. Set)
					   (t. ∀A P B. t = ((A, x. P.[x]), B) ⟹ ∀x ∈ Set. x ∈ B ⟺ x ∈ A ∧ P.[x]),
					THEN ex_elim];
				simp;
				- for p A P if p, A;
					apply separation_ex1[OF A, THEN in.ex1_cong[THEN iff_elim1, OF eq.refl _ (1)], of (x. P.[x])];
					simp p;
					- for B if Bty;
						apply iff_intro;
						- if B for A' P' B' if A', P', B';
							fold A' unbind_cong[OF P'] B';
							by B.
						- if imp;
							apply imp;
							simp.
						.
					.
				- for CollectIn if C;
					apply assm[of CollectIn];
					- show Cset: for A P if A: A ∈ Set then {x ∈ A. P.[x]} ∈ Set;
						apply C[THEN and_elim1, of (A, x. P.[x]) A P, simp, OF A].
					- for A P if A for x;
						note(simp) C[THEN and_elim2, of (A, x. P.[x]) A P, simp, OF A eq.refl eq.refl eq.refl, rule].
						apply iff_intro;
						- if xC;
							have! x ∈ Set;
								apply in_set_imp_set[OF Cset[OF A] xC].
							use xC.
						-> if xA;
							have! x ∈ Set;
								apply in_set_imp_set[OF A xA].
							use xA.
						.
					.
				.
			.
		.
end

---
### Image and Replacement

Image and replacement are equivalent.
---
theory Image:
	assume image_ex: ∀f.
		∀A ∈ Set. (∀x ∈ A. f x ∈ Set) ⟹ ∃B ∈ Set. ∀y ∈ Set. y ∈ B ⟺ (∃x ∈ A. y = f x).
begin

	lemma image_ex1: for f
		if A! A ∈ Set, f: ∀x ∈ A. f x ∈ Set
		then ∃!B ∈ Set. ∀y ∈ Set. y ∈ B ⟺ (∃x ∈ A. y = f x);
		-	apply image_ex[rule, OF A f[rule], THEN in.ex_elim];
			- for B if B! B ∈ Set, inB: ∀y ∈ Set. y ∈ B ⟺ (∃x ∈ A. y = f x);
				apply+ in.ex1_intro1[of B] in.all_intro;
				- by inB[rule].
				-.
				- for B' if ! B' ∈ Set, inB': ∀y ∈ Set. y ∈ B' ⟺ (∃x ∈ A. y = f x) then B' = B;
					by set_eq_intro #simp inB[rule] inB'[rule].
				.
			.
		.

	obtain (`) where
		image_Set: if A ∈ Set, ∀x ∈ A. f x ∈ Set then f ` A ∈ Set,
		image_iff: if A ∈ Set, ∀x ∈ A. f x ∈ Set, y ∈ Set then y ∈ f ` A ⟺ (∃x ∈ A. y = f x);
		- for thesis if assm;
			apply unique_choice_cond[
				of (p. ∃f. ∃A ∈ Set. p = (f,A) ∧ (∀x ∈ A. f x ∈ Set))
				   (p. Set)
				   (((f,A),B). ∀y ∈ Set. y ∈ B ⟺ (∃x ∈ A. y = f x)),
				simp, THEN ex_elim];
			- by image_ex1.
			- for (`) if im;
				apply assm[of (`)];
				- if A: A ∈ Set, f: ∀x ∈ A. f x ∈ Set;
					use im[OF A eq.refl f].
				- if A: A ∈ Set, f: ∀x ∈ A. f x ∈ Set;
					use im[OF A eq.refl f];.
				.
			.
		.

end

theory ReplacementSchema:
	assume replacement_schema:
		∀P. ∀A ∈ Set. (∀x ∈ A. ∃!y ∈ Set. P.[x,y]) ⟹ ∃B ∈ Set. ∀y ∈ Set. y ∈ B ⟺ (∃x ∈ A. P.[x,y]).
begin

	lemma replacement_ex1: for P A
		if A: A ∈ Set, ex1: ∀x. x ∈ A ⟹ ∃!y ∈ Set. P.[x,y] then ∃!B ∈ Set. ∀y ∈ Set. y ∈ B ⟺ (∃x ∈ A. P.[x,y]);
		apply replacement_schema[rule, OF A ex1, THEN in.ex_elim];
		- for B if B!, inB;
			apply in.ex1_intro1[of B];
			apply inB;
			apply B;
			- for B' if B'!, inB';
				apply set_eq_intro;
				simp inB[rule] inB'[rule].
			.
		.

	interpret Image;
		-> for f A if A, f;
			apply replacement_ex1[of ((x,y). y = f x), OF A, THEN in.ex1_elim];
			simp in.ex1_eq_iff;
			- by f.
			- for B if B, Biff, uniq;
				by in.ex_intro1[OF B] #simp Biff[rule].
			.
		.
end

context Image begin
	---
	As we have already assumed unique choice, the replacement schema is derivable:
	---
	interpret: ReplacementSchema;
		-> for P A if A, ex1;
			- apply unique_choice_cond[of (x. x ∈ A) (x. Set) P, THEN ex_elim];
				- by ex1.
				- for f if f;
					have Pf: for x y if x: x ∈ A, y: y ∈ Set then P.[x,y] ⟺ y = f x;
						have fx: f x ∈ Set;
							use f[OF x].
						have Pfx: P.[x, f x];
							use f[OF x].
						unfold ex1[OF x, THEN in.ex1_imp_iff_eq, OF fx Pfx y];
						by iff_eq.commute.
					apply image_ex[of f, rule, OF A, THEN in.ex_elim];
					- for x if x; use f[OF x].
					- for B if B, B_iff;
						apply in.ex_intro1[OF B];
						simp B_iff[rule] Pf.
					.
				.
			.
		.
end
