---
# Equality
---

import Base.

fix (=).

namespace eq:
	import MetaReflexive (=).
	assume elim: for X y z if y = z, X.[y] then X.[z].
end

begin
---
## Theorems
---

note! eq.refl.

interpret MetaMagmas (=).

---
Equality is an equivalence.
---
context eq begin
	interpret MetaEquivalence (=);
		- for x y if xy: x = y then y = x;
			by elim[of (z. z = x), OF xy].
		- for x y z if xy: x = y, yz: y = z then x = z;
			by elim[of (w. x = w), OF yz xy].
		.
	lemma cong_meta: for X if yz: y = z then X.[y] = X.[z];
		by elim[of (w. X.[y] = X.[w]), OF yz refl].
	lemma imp: if PQ: P = Q, P: P then Q;
		by elim[of (x. x), OF PQ P].

	lemma imp_rev: if PQ: P = Q, Q: Q then P;
		by imp[OF sym[OF PQ] Q].
end

set rewrite eq.imp eq.imp_rev eq.refl eq.trans.
set dual eq.sym.

lemma arg_cong: if xy: x = y then f x = f y;
	by eq.cong_meta[of (z. f z), OF xy].

lemma fun_cong: if fg: f = g then f x = g x;
	by eq.cong_meta[of (h. h x), OF fg].

context eq begin
	lemma cong: for f x if fg: f = g, xy: x = y then f x = g y;
		have 1: f x = f y;
			by arg_cong[OF xy].
		apply trans[OF 1];
		by fun_cong[OF fg].
end

note(cong) eq.cong.

---
## Theories
---

theory Iff:
	import Iff.
begin
	lemma eq_imp_iff: if eq: P = Q then P ⟺ Q;
		by iff_intro #unfold(=) eq.
end

theory Id: -- I combinator
	fix id.
	assume id_eq: id x = x.
end

theory Const: -- K combinator
	fix const.
	assume const_eq: const x y = x.
end

theory TwoValued:
	assume imp_imp_eq: if P, Q then P = Q.
	assume imp_eq: if P then (P ⟹ Q) = Q.
begin
	obtain true where true_intro: true;
	- for thesis if assm;
		apply assm[of (∀P. P ⟹ P)].
	.
	lemma eq_true: if P: P then P = true;
		by imp_imp_eq[OF P true_intro].
	lemma true_eq: if P: P then true = P;
		unfold eq_true[OF P].
	lemma eq_refl_eq_true: (x = x) = true;
		by eq_true.
	lemma weaken_eq: (P ⟹ Q ⟹ P) = true;
		by eq_true.
	lemma imp_true_eq: (P ⟹ true) = true;
		by eq_true true_intro.
	lemma true_imp_eq: (true ⟹ P) = P;
		by imp_eq[OF true_intro].
end

theory MetaInjective:
	fix f.
	assume inj: if f x = f x' then x = x'.
end

theory MetaInverse:
	fix f f⁻.
	assume inverse: f⁻ (f x) = x.
begin
	interpret MetaInjective;
		- for x x' if eq: f x = f x';
			have 1: f⁻ (f x) = f⁻ (f x');
				unfold eq.
			by 1[unfolded inverse].
		.
end

theory Pair: --- Syntactic Pairing ---
	fix (,) fst snd.
	assume fst: fst (x,y) = x.
	assume snd: snd (x,y) = y.
begin
	interpret pair: MetaInjective (,);
		- for x x' if eq: (,) x = (,) x' then x = x';
			have 1: fst (x,x) = fst (x',x);
				unfold eq.
			by 1[unfolded fst].
		.
	lemma pair_eq_pair_imp1: if eq: (x,y) = (x',y') then x = x';
		have 1: x = fst (x,y);
			unfold fst.
		apply eq.trans[OF 1];
		have 2: fst (x,y) = fst (x',y');
			unfold eq.
		apply eq.trans[OF 2];
		have 3: fst (x',y') = x';
			unfold fst.
		by eq.trans[OF 3].

	lemma pair_eq_pair_imp2: if eq: (x,y) = (x',y') then y = y';
		have 1: y = snd (x,y);
			unfold snd.
		apply eq.trans[OF 1];
		have 2: snd (x,y) = snd (x',y');
			unfold eq.
		apply eq.trans[OF 2];
		have 3: snd (x',y') = y';
			unfold snd.
		by eq.trans[OF 3].

end

theory If:
	fix If.
	assume If_then: for P x y if P then If P x y = x.
	---
	A minimal specification: P and ¬P will not lead to explosion.
	---
	assume If_else: if P ⟹ x = y then If P x y = y.
begin
end

theory Ex1:
	fix (∃!).
	assume ex1_intro1: for x P if P.[x], ∀y. P.[y] ⟹ y = x then ∃!x. P.[x].
	assume ex1_elim: if ∃!x. P.[x] then for Q if ∀x. P.[x] ⟹ (∀y. P.[y] ⟹ y = x) ⟹ Q then Q.
begin
	lemma ex1_intro: if assm: ∀Q. (∀x. P.[x] ⟹ (∀y. P.[y] ⟹ y = x) ⟹ Q) ⟹ Q then ∃!x. P.[x];
		apply assm;
		- for x if Px;
			by ex1_intro1[OF Px].
		.
end

theory The:
	import Ex1.
	fix (THE).
	assume ex1_imp_THE: (∃!x. P.[x]) ⟹ P.[THE x. P.[x]].
begin
	lemma THE_eq_intro: if ex1: ∃!y. P.[y], Px: P.[x] then (THE y. P.[y]) = x;
		apply ex1_elim[OF ex1];
		- for z if Pz: P.[z], 1: ∀y. P.[y] ⟹ y = z;
			have zT: (THE x. P.[x]) = z;
				by 1[OF ex1_imp_THE[OF ex1]].
			unfold zT;
			unfold 1[OF Px].
		.
	note eq_THE_intro: THE_eq_intro[THEN eq.sym].
end

theory Minimal:
	import Minimal.
	import Ex1.
begin
	lemma ex1_imp_ex: if ex1: ∃!x. P.[x] then ∃x. P.[x];
		apply ex1_elim[OF ex1];
		- for x;
			by ex_intro1[of x].
		.
	lemma ex1_iff: (∃!x. P.[x]) ⟺ (∃x. P.[x] ∧ (∀y. P.[y] ⟹ y = x));
		apply iff_intro;
		- if ex1;
			apply ex_intro;
			- for Q;
				unfold and_imp_iff_imp_imp;
				apply ex1_elim[OF ex1]=.
			.
		- if ex;
			apply ex1_intro;
			- for Q;
				apply ex[unfolded ex_iff and_imp_iff_imp_imp]=.
			.
		.
	namespace iff:
		lemma ex1_cong:
			if iff: ∀x. P.[x] ⟺ P'.[x] then (∃!x. P.[x]) ⟺ (∃!x. P'.[x]);
			unfold ex1_iff iff.
	end
	note(cong) iff.ex1_cong.
	theory Class:
		import Collect.
		assume Collect_eq_intro: if ∀x. P x ⟺ P' x then Collect P = Collect P'.
	begin
		---
		Paradoxical classes e.g. {x. ¬ x x} contain untyped elements, so they will not be equal to typeable classes.
		---
	end
end

theory Intuitionistic:
	import Minimal.
	import Intuitionistic.
begin
	namespace iff:
		interpret eq: iff.MetaCommutative (=);
			by iff_intro[OF eq.sym eq.sym].
	end
end

theory Ext:
	assume ext: if ∀x ∈ A. f x = g x, A ∈ EQTYPE, B ∈ EQTYPE, f ∈ A → B, g ∈ A → B
	then f = g.
end

theory UnaryAbstraction:
	---
	For any term with a free variable `x`,
	we assume one can introduce a symbol `f` such that `f x` is equal to the term.
	---
	assume abst: if ∀f. (∀x. f x = F.[x]) ⟹ P then P.
begin
	interpret Id;
		obtain id where id_eq: id x = x;
			- for thesis;
				apply abst[of (x. x)]=.
			.
		.
	note(unfold) id_eq.
	---
	One can obtain the type-free existential quantifier as a unary abstraction.
	---
	interpret Ex;
		obtain (∃) where
			ex_intro1: ∀x P. P.[x] ⟹ ∃x. P.[x],
			ex_elim: (∃x. P.[x]) ⟹ ∀Q. (∀x. P.[x] ⟹ Q) ⟹ Q;
			- for thesis if assm;
				apply abst[of (P. (∀Q. (∀x. P.[x] ⟹ Q) ⟹ Q))];
				- for (∃) if eq: ∀P. (∃) P = (∀ Q. (∀x. P.[x] ⟹ Q) ⟹ Q);
					apply assm[of (∃)];
					- for x P if Px: P.[x] then ∃x. P.[x];
						unfold eq;
						- for Q if imp: ∀x. P.[x] ⟹ Q then Q;
							by imp[OF Px].
						.
					- for P if ex: ∃x. P.[x];
						- for Q if imp: ∀x. P.[x] ⟹ Q then Q;
							apply ex[unfolded eq];
							by #elim imp.
						.
					.
				.
			.
		.
	lemma ex_abst: ∃f. ∀x. f x = F.[x];
		apply ex_intro[OF abst].
	interpret Ex1;
		obtain (∃!) where
			ex1_intro1: ∀x P. P.[x] ⟹ (∀y. P.[y] ⟹ y = x) ⟹ ∃!x. P.[x],
			ex1_elim: (∃!x. P.[x]) ⟹ ∀Q. (∀x. P.[x] ⟹ (∀y. P.[y] ⟹ y = x) ⟹ Q) ⟹ Q;
			- for thesis if assm;
				apply abst[of (P. ∀Q. (∀x. P.[x] ⟹ (∀y. P.[y] ⟹ y = x) ⟹ Q) ⟹ Q)];
				- for (∃!) if eq;
					apply assm[of (∃!)];
					- for x P if Px, imp_eq;
						unfold eq;
						- for Q if imp;
							by imp[of x] Px imp_eq.
						.
					- for P if ex1;
						- for Q;
							apply ex1[unfolded(=) eq]=.
						.
					.
				.
			.
		.
	obtain inj where
		inj_elim1: inj f ⟹ ∀x y. f x = f y ⟹ x = y,
		inj_intro: (∀x y. f x = f y ⟹ x = y) ⟹ inj f;
		- for thesis if assm;
			apply abst[of (f. (∀x y. f x = f y ⟹ x = y))];
			- for inj if eq;
				apply assm[of inj];
				- for f;
					unfold eq.
				- for f;
					unfold eq.
				.
			.
		.
	lemma id_inj: inj id;
		apply inj_intro.
	lemma inj_imp_ex1: if f: inj f then for x, ∃!x'. f x' = f x;
		apply ex1_intro1[of x];
		by inj_elim1[OF f].
	---
	There exists an injection, as exemplified by `id`.
	---
	lemma ex_inj: ∃f. inj f;
		apply ex_intro;
		- for P if assm;
			apply assm[OF id_inj].
		.
	---
	Having operator `THE` allows one to pick an inverse of an injection.
	---
	theory The:
		import The.
	begin
	lemma inj_imp_ex_inv: if f: inj f then ∃g. ∀x. g (f x) = x;
		apply ex_intro;
		- for thesis if assm;
			apply abst[of (y. THE z. f z = y)];
			- for g if eq;
				apply assm[of g];
				- for x;
					unfold eq;
					apply inj_elim1[OF f];
					apply ex1_imp_THE[of (z. f z = f x)];
					apply inj_imp_ex1[OF f].
				.
			.
		.
		--- obtain (∋) where
			Collect_has_intro: P x ⟹ Collect P ∋ x,
			Collect_has_elim1: Collect P ∋ x ⟹ P x;
			- for thesis if assm;
				apply Collect_inj[THEN inj_imp_ex_inv, THEN ex_elim];
				- for (∋) if eq;
					apply assm[of (∋)];
					- for P x;
						unfold eq.
					- for P x;
						unfold eq.
					.
				.
			. ---
	end
end
