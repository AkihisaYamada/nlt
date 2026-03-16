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
Extensionality as an inference rule:
---
lemma set_eq_intro: if eq: ∀x. x ∈ Set ⟹ x ∈ A ⟺ x ∈ B, A! A ∈ Set, B! B ∈ Set then A = B;
	by extensionality_axiom[rule, OF A B] eq.

lemma all_in_set_iff: if A: A ∈ Set then (∀x ∈ Set. x ∈ A ⟹ P.[x]) ⟺ (∀x ∈ A. P.[x]);
	apply iff_intro;
	-> if P, xA: x ∈ A then P.[x];
		by P[OF _ xA] in_set_imp_set[OF A xA].
	-> if P, xSet: x ∈ Set, xA: x ∈ A then P.[x];
		by P[OF xA].
	.

lemma ex_in_set_iff: if A: A ∈ Set then (∃x ∈ Set. x ∈ A ∧ P.[x]) ⟺ (∃x ∈ A. P.[x]);
	apply iff_intro;
	-> for x; by in.ex_intro1[of x].
	-> for x; by in.ex_intro1[of x] in_set_imp_set[OF A].
	.

---
## Theories

### Empty Set
---
theory EmptySetAxiom:
	assume ex_empty: ∃x ∈ Set. ¬(∃y ∈ Set. y ∈ x).
end

theory EmptySet:
	fix empty.
	assume empty_Set! {} ∈ Set.
	assume not_in_empty: ¬ x ∈ {}.
begin

	lemma in_empty_imp_false: if x0: x ∈ {} then false;
		by not_imp_false[OF not_in_empty x0].

	interpret: EmptySetAxiom;
		- by in.ex_intro1[of {}] not_intro #elim in_empty_imp_false.
		.

end

context EmptySetAxiom begin

	interpret EmptySet;
		obtain empty where empty_Set! {} ∈ Set, nexIn_empty: ¬(∃x ∈ Set. x ∈ {});
			- for thesis;
				apply in.ex_elim[OF ex_empty]>0.
			.
		-> if x0: x ∈ {};
			by nexIn_empty[rule, OF _ x0] in_set_imp_set[OF _ x0].
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

theory UnorderedPairAxiom:
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
---
theory UnorderedPair:
	fix upair.
	assume upair_Set! if x ∈ Set, y ∈ Set then upair(x,y) ∈ Set.
	assume upair_iff: if x ∈ Set, y ∈ Set then z ∈ upair(x,y) ⟺ z = x ∨ z = y.
begin

	lemma upair_intro1! if !x ∈ Set, !y ∈ Set then x ∈ upair(x,y);
		simp upair_iff.
	lemma upair_intro2! if !x ∈ Set, !y ∈ Set then y ∈ upair(x,y);
		simp upair_iff.
	lemma upair_elim: if x: x ∈ upair(y,z), y: x = y ⟹ P, z: x = z ⟹ P, !y ∈ Set, !z ∈ Set then P;
		apply x[unfold upair_iff, THEN or_elim];
		by #elim y z.

	lemma ExIn_upair_iff: if !x ∈ Set, !y ∈ Set then (∃z ∈ upair(x,y). P.[z]) ⟺ P.[x] ∨ P.[y];
		apply iff_intro;
		note(cong) eq_cong_meta[of P].
		-> for z if z;
			apply upair_elim[OF z];
			- if (simp).
			- if (simp).
			.
		- if or;
			apply or_elim[OF or];
			- by in.ex_intro1[of x].
			- by in.ex_intro1[of y].
			.
		.


	interpret UnorderedPairAxiom;
		-> if ! x ∈ Set, ! y ∈ Set;
			apply in.ex_intro1[of (upair(x,y))];
			by #simp upair_iff.
		.
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

extend UniqueChoiceCond begin
	extend UnorderedPairAxiom begin
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
						- if x: x ∈ Set, y: y ∈ Set; use f[OF x y eq.refl].
						- if x: x ∈ Set, y: y ∈ Set for z;
							note fxy: f[OF x y eq.refl].
							note fset: fxy[THEN and_elim1].
							note fiff: fxy[THEN and_elim2, rule].
							apply iff_intro;
							- if zf;
								by zf[unfold fiff[OF in_set_imp_set[OF fset zf]]].
							- if or;
								apply or_elim[OF or];
								- if zx; by x #simp fiff zx.
								- if zy; by y #simp fiff zy.
								.
							.
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
end

theory CollectIn:
	fix CollectIn.
	assume CollectIn! for A P if A ∈ Set then {x ∈ A. P.[x]} ∈ Set.
	assume CollectIn_iff: for A P if A ∈ Set then x ∈ {x ∈ A. P.[x]} ⟺ x ∈ A ∧ P.[x].
begin
	interpret SeparationSchema;
		-> for P A if !;
			apply in.ex_intro1[of {x ∈ A. P.[x]}];
			by #simp CollectIn_iff.
		.
end

context UniqueChoiceCond begin
	extend SeparationSchema begin
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
end

---
### Image and Replacement

Image and replacement are equivalent modulo unique choice.
---
theory ImageSchema:
	assume image_schema: ∀f.
		∀A ∈ Set. (∀x ∈ A. f x ∈ Set) ⟹ ∃B ∈ Set. ∀y ∈ Set. y ∈ B ⟺ (∃x ∈ A. y = f x).
begin

	lemma image_ex: for f
		if A! A ∈ Set, f: ∀x ∈ A. f x ∈ Set
		then ∃B ∈ Set. ∀y. y ∈ B ⟺ (∃x ∈ A. y = f x);
		apply image_schema[rule, OF A f[rule], THEN in.ex_elim];
		- for B if B!, Bspec;
			apply in.ex_intro1[OF B];
			- for y;
				apply iff_intro;
				- if yB: y ∈ B;
					have y! y ∈ Set;
						by in_set_imp_set[OF B yB].
					by yB[unfold Bspec[rule]].
				-> if xA! x ∈ A, yfx: y = f x;
					have y! y ∈ Set;
						by f[rule] #simp yfx.
					by in.ex_intro1[OF xA] #simp Bspec[rule] yfx.
				.
			.
		.
	lemma image_ex1: for f
		if A! A ∈ Set, f: ∀x ∈ A. f x ∈ Set
		then ∃!B ∈ Set. ∀y. y ∈ B ⟺ (∃x ∈ A. y = f x);
		-	apply image_ex[OF A f, THEN in.ex_elim];
			- for B if B! B ∈ Set, inB: ∀y. y ∈ B ⟺ (∃x ∈ A. y = f x);
				apply in.ex1_intro1[of B];
				- by inB.
				-.
				- for B' if ! B' ∈ Set, inB': ∀y. y ∈ B' ⟺ (∃x ∈ A. y = f x) then B' = B;
					by set_eq_intro #simp inB inB'.
				.
			.
		.

end

theory Image:
	fix (`).
	assume image_Set: if A ∈ Set, ∀x ∈ A. f x ∈ Set then f ` A ∈ Set.
	assume image_iff: if A ∈ Set, ∀x ∈ A. f x ∈ Set then y ∈ f ` A ⟺ (∃x ∈ A. y = f x).
begin
	interpret ImageSchema;
		-> for f A if A!, f!;
			apply in.ex_intro1[of (f ` A)];
			- by image_Set.
			- by #simp image_iff.
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

	interpret ImageSchema;
		-> for f A if A, f;
			apply replacement_ex1[of ((x,y). y = f x), OF A, THEN in.ex1_elim];
			simp in.ex1_eq_iff;
			- by f.
			- for B if B, Biff, uniq;
				by in.ex_intro1[OF B] #simp Biff[rule].
			.
		.
end

context UniqueChoiceCond begin
	extend ImageSchema begin
		interpret Image;
			obtain (`) where
				image_Set: if A ∈ Set, ∀x ∈ A. f x ∈ Set then f ` A ∈ Set,
				image_iff: if A ∈ Set, ∀x ∈ A. f x ∈ Set then y ∈ f ` A ⟺ (∃x ∈ A. y = f x);
				- for thesis if assm;
					apply unique_choice_cond[
						of (p. ∃f. ∃A ∈ Set. p = (f,A) ∧ (∀x ∈ A. f x ∈ Set))
						   (p. Set)
						   (((f,A),B). ∀y. y ∈ B ⟺ (∃x ∈ A. y = f x)),
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
			.
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
							simp B_iff Pf.
						.
					.
				.
			.
	end
	extend ReplacementSchema begin
		interpret ImageSchema.
	end
end

---
### Power Set
---
theory PowerSetAxiom:
	assume Pow_axiom: ∀A ∈ Set. ∃B ∈ Set. ∀X ∈ Set. X ∈ B ⟺ (∀y ∈ X. y ∈ A).
begin

	lemma Pow_ex: if A: A ∈ Set then ∃B ∈ Set. ∀X. X ∈ B ⟺ X ∈ Set ∧ (∀y ∈ X. y ∈ A);
		obtain B where
			Bset: B ∈ Set,
			B: ∀X ∈ Set. X ∈ B ⟺ (∀w ∈ X. w ∈ A);
			- for thesis;
				apply Pow_axiom[rule, OF A, THEN in.ex_elim]>0.
			.
		apply in.ex_intro1[OF Bset];
		- for X;
			apply iff_intro;
			- if XB: X ∈ B;
				have ! X ∈ Set;
					by in_set_imp_set[OF Bset XB].
				by XB[unfold B[rule], rule].
			-> if Xset: X ∈ Set, sub;
				unfold B[rule, OF Xset];
				by sub.
			.
		.

	lemma Pow_ex1: if A! A ∈ Set then ∃!B ∈ Set. ∀X. X ∈ B ⟺ X ∈ Set ∧ (∀y ∈ X. y ∈ A);
		apply Pow_ex[OF A, THEN in.ex_elim];
		- for B if B!, Bspec;
			apply in.ex1_intro1[of B];
			apply Bspec=;
			apply B;
			- for B' if B'!, B'spec;
				by set_eq_intro #simp Bspec B'spec.
			.
		.
end

theory Pow:
	fix Pow.
	assume Pow_Set! if A ∈ Set then Pow A ∈ Set.
	assume Pow_iff: if A ∈ Set then X ∈ Pow A ⟺ X ∈ Set ∧ (∀y ∈ X. y ∈ A).
begin
	interpret PowerSetAxiom;
		-> if ! A ∈ Set;
			apply in.ex_intro1[of (Pow A)];
			by #simp Pow_iff.
		.
end


context UniqueChoiceCond begin
	extend PowerSetAxiom begin
		interpret Pow;
			obtain Pow where
				Pow_Set: if A ∈ Set then Pow A ∈ Set,
				Pow_iff: if A ∈ Set then X ∈ Pow A ⟺ X ∈ Set ∧ (∀y ∈ X. y ∈ A);
				- for thesis if assm;
					apply unique_choice_cond[of
							(A. A ∈ Set)
							(A. Set)
							((A,B). ∀X. X ∈ B ⟺ X ∈ Set ∧ (∀y ∈ X. y ∈ A)),
						THEN ex_elim, simp];
					- by Pow_ex1.
					- for f if f;
						apply assm[of f];
						- if A: A ∈ Set;
							use f[OF A].
						- if A: A ∈ Set;
							use f[OF A]; .
						.
					.
				.
			.
	end
end

---
### Unions
---
theory UnionAxiom:
	assume CUP_axiom: ∀AA ∈ Set. ∃B ∈ Set. ∀x ∈ Set. x ∈ B ⟺ (∃A ∈ Set. A ∈ AA ∧ x ∈ A).
begin

	lemma CUP_ex: if AA! AA ∈ Set then ∃B ∈ Set. ∀x. x ∈ B ⟺ (∃A ∈ AA. x ∈ A);
		apply CUP_axiom[rule, OF AA, THEN in.ex_elim];
		- for B if Bset, Bspec;
			apply in.ex_intro1[OF Bset];
			- for x;
				apply iff_intro;
				- if xB: x ∈ B;
					have! x ∈ Set;
						by in_set_imp_set[OF Bset xB].
					apply xB[unfold Bspec[rule], THEN in.ex_elim];
					- for A; by in.ex_intro1[of A].
					.
				-> if A: A ∈ AA, xA: x ∈ A;
					have! A ∈ Set;
						apply in_set_imp_set[OF AA A].
					have! x ∈ Set;
						apply in_set_imp_set[OF _ xA].
					unfold Bspec[rule];
					by in.ex_intro1[of A] A xA.
				.
			.
		.

	lemma CUP_ex1: if AA! AA ∈ Set then ∃!B ∈ Set. ∀x. x ∈ B ⟺ (∃A ∈ AA. x ∈ A);
		apply CUP_ex[OF AA, THEN in.ex_elim];
		- for B if B!, Bspec;
			apply in.ex1_intro1[of B];
			- apply Bspec=.
			- apply B.
			- for B' if B'!, B'spec;
				apply set_eq_intro;
				by #simp Bspec B'spec.
			.
		.
end

theory CUP:
	fix (⋃).
	assume CUP_Set! if AA ∈ Set then ⋃AA ∈ Set.
	assume CUP_iff: if AA ∈ Set then x ∈ ⋃AA ⟺ (∃A ∈ AA. x ∈ A).
begin

	lemma ExIn_CUP(simp) if AA! AA ∈ Set then (∃x ∈ ⋃AA. P.[x]) ⟺ (∃A ∈ AA. ∃x ∈ A. P.[x]);
		simp in.ex_def CUP_iff;
		apply iff_intro;
		-> for x A if ! A ∈ AA, ! x ∈ A, ! P.[x];
			apply ex_intro1[of A];
			apply ex_intro1[of x].
		-> if ! A ∈ AA, ! x ∈ A, ! P.[x];
			apply ex_intro1[of x];
			apply ex_intro1[of A].
		.

	interpret UnionAxiom;
		-> if AA! AA ∈ Set;
			apply in.ex_intro1[OF CUP_Set[OF AA]];
			by #simp ex_in_set_iff CUP_iff.
		.

end

context UniqueChoiceCond begin
	extend UnionAxiom begin
		interpret CUP;
			obtain (⋃) where
				CUP_Set! if AA ∈ Set then ⋃AA ∈ Set,
				CUP_iff: if AA ∈ Set then x ∈ ⋃AA ⟺ (∃A ∈ AA. x ∈ A);
				- for thesis if assm;
					apply unique_choice_cond[of
							(AA. AA ∈ Set)
							(AA. Set)
							((AA,B). ∀x. x ∈ B ⟺ (∃A ∈ AA. x ∈ A)),
						simp, OF CUP_ex1, THEN ex_elim];
					- for f if f;
						apply assm[of f];
						- for x if x;
							use f[OF x].
						- for x if x;
							use f[OF x].
						.
					.
				.
			.
	end
end

theory Cup:
	fix (∪).
	assume cup_Set! if A ∈ Set, B ∈ Set then A ∪ B ∈ Set.
	assume cup_iff: if A ∈ Set, B ∈ Set then x ∈ A ∪ B ⟺ x ∈ A ∨ x ∈ B.
begin
end

context AbbrevCond begin
	extend CUP begin
		extend UnorderedPair begin
			interpret Cup;
				obtain (∪) where
					cup_Set! if A ∈ Set, B ∈ Set then A ∪ B ∈ Set,
					cup_iff: if A ∈ Set, B ∈ Set then x ∈ A ∪ B ⟺ x ∈ A ∨ x ∈ B;
					- for thesis if assm;
						apply abbrev_cond[of (p. ∃A ∈ Set. ∃B ∈ Set. p = (A,B)) (p. Set) ((A,B). ⋃(upair(A,B))), simp];
						- by in.all_intro.
						- for (∪) if cup;
							apply assm[of (∪)];
							by #simp cup[OF _ _ eq.refl] CUP_iff ExIn_upair_iff.
						.
					.
				.
		end
	end
end


---
### Infinity
---
theory InfinityAxiom:
	import EmptySet.
	import SingletonSet.
	assume infinity_axiom: ∃x ∈ Set. {} ∈ x ∧ (∀y ∈ x. y ∪ {y}).
end

---
### Foundation
---
theory FoundationAxiom:
	import EmptySet.
	assume foundation_axiom: ∀x ∈ Set. ¬ x = {} ⟹ ∃y ∈ Set. x ∈ y ∧ (∀z ∈ Set. z ∈ x ⟹ ¬ z ∈ y).
end
