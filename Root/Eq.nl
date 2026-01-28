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
		- if xy: x = y then y = x;
			by elim[of (z. z = x), OF xy].
		- if xy: x = y, yz: y = z then x = z;
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
	lemma cong: if fg: f = g, xy: x = y then f x = g y;
		have 1: f x = f y;
			by arg_cong[OF xy].
		apply trans[OF 1];
		by fun_cong[OF fg].
end

note(fallback) eq.cong.

---
## Theories
---

theory Id: -- I combinator
	fix id.
	assume id_eq(simp) id x = x.
end

theory Const: -- K combinator
	fix const.
	assume const_eq(simp) const x y = x.
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
	assume ex1_elim: if ∃!x. P.[x], ∀x. P.[x] ⟹ (∀y. P.[y] ⟹ y = x) ⟹ Q then Q.
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

theory Iff:
	import Iff.
begin
	lemma eq_imp_iff(fallback) if eq: P = Q then P ⟺ Q;
		unfold[on (=)] eq;
		.
end

theory Membership:
	import Membership.
begin
	interpret Magmas.
	theory Antisymmetric:
		fix A (≤).
		assume antisym: if x ≤ y, y ≤ x, x ∈ A, y ∈ A then x = y.
	begin
		interpret Attractive;
			- if xy: x ≤ y, yx: y ≤ x, yz: y ≤ z, x: x ∈ A, y: y ∈ A, z: z ∈ A then x ≤ z;
				unfold antisym[OF xy yx x y];
				by yz.
			- if xy: x ≤ y, yx: y ≤ x, xz: x ≤ z, x: x ∈ A, y: y ∈ A, z: z ∈ A then y ≤ z;
				unfold antisym[OF yx xy y x];
				by xz.
			.
	end
	theory PseudoOrder:
		import Reflexive.
		import Antisymmetric.
	end
	theory Order:
		import Preorder.
		import Antisymmetric.
	begin
		interpret PseudoOrder.
	end
	theory Idempotent:
		fix A (*).
		assume idem: if x ∈ A then x * x = x.
	end
end

theory Minimal:
	import Iff.
	import Minimal.
	import Ex1.
begin
	lemma eq_refl_iff(simp) x = x ⟺ true;
		by iff_intro.
	lemma ex1_imp_ex: if ex1: ∃!x. P.[x] then ∃x. P.[x];
		apply ex1_elim[OF ex1];
		- for x;
			by ex_intro1[of x].
		.
	lemma ex1_iff: (∃!x. P.[x]) ⟺ (∃x. P.[x] ∧ (∀y. P.[y] ⟹ y = x));
		apply iff_intro;
		- if ex1;
			apply ex_intro;
			unfold and_imp_iff_imp_imp;
			apply ex1_elim[OF ex1]=.
		- if ex;
			apply ex1_intro;
			apply ex[unfolded ex_iff and_imp_iff_imp_imp]=.
		.
	lemma ex1_cong_iff(cong)
		if iff: ∀x. P.[x] ⟺ P'.[x] then (∃!x. P.[x]) ⟺ (∃!x. P'.[x]);
		unfold ex1_iff iff.
	theory MetaReflexive:
		import Minimal.MetaReflexive.
	end
	theory MetaPreorder:
		import Minimal.MetaPreorder.
	begin
		interpret .MetaReflexive.
	end
	theory Membership:
		import Membership.
	begin
		theory AllIn:
			import AllIn.
		begin
			lemma allIn_cong_iff(cong)
				if AB: A = B, PQ: ∀x. x ∈ B ⟹ P.[x] ⟺ Q.[x]
				then (∀x ∈ A. P.[x]) ⟺ (∀x ∈ B. Q.[x]);
				apply iff_intro;
				- if PA;
					apply allIn_intro;
					by allIn_elim1[OF PA, unfolded AB] #fold PQ.
				- if QB;
					apply allIn_intro;
					by allIn_elim1[OF QB] #unfold AB PQ.
				.
		end
		theory ExIn:
			import ExIn.
		begin
			lemma exIn_cong_iff(cong)
				if AB: A = B, PQ: ∀x. x ∈ B ⟹ P.[x] ⟺ Q.[x]
				then (∃x ∈ A. P.[x]) ⟺ (∃x ∈ B. Q.[x]);
				apply iff_intro;
				- if PA;
					apply exIn_elim[OF PA];
					- for x;
						by exIn_intro1[of x] #unfold AB #fold PQ.
					.
				- if QB;
					apply exIn_elim[OF QB];
					- for x;
						by exIn_intro1[of x] #unfold AB PQ.
					.
				.
		end
		theory Ex1In:
			fix (∃!∈).
			import AllIn.
			import ExIn.
			assume ex1In_iff: (∃!x ∈ A. P.[x]) ⟺ (∃x ∈ A. P.[x] ∧ (∀y ∈ A. P.[y] ⟹ y = x)).
		begin
			lemma ex1In_cong_iff(cong)
				if iff: ∀x. x ∈ A ⟹ P.[x] ⟺ P'.[x] then (∃!x ∈ A. P.[x]) ⟺ (∃!x ∈ A. P'.[x]);
				unfold ex1In_iff iff.
			lemma ex1In_intro1:
				for x A P if Px: P.[x], x: x ∈ A, uniq: ∀y ∈ A. P.[y] ⟹ y = x then ∃!x ∈ A. P.[x];
				unfold ex1In_iff;
				by exIn_intro1[of x] Px x uniq.

			lemma ex1In_elim: if ex1: ∃!x ∈ A. P.[x], imp: ∀x. x ∈ A ⟹ P.[x] ⟹ (∀y ∈ A. P.[y] ⟹ y = x) ⟹ Q then Q;
				apply ex1[unfolded ex1In_iff, THEN exIn_elim];
				unfold and_imp_iff_imp_imp;
				- for x;
					by imp[of x].
				.
		end
		theory TheIn:
			fix THE.∈.
			import Ex1In.
			assume TheIn_intro: (∃!x ∈ A. P.[x]) ⟹ P.[THE x ∈ A. P.[x]].
			assume TheIn_in: (∃!x ∈ A. P.[x]) ⟹ (THE x ∈ A. P.[x]) ∈ A.
		begin
			lemma TheIn_eq_intro: if ex1: ∃!y ∈ A. P.[y], Px: P.[x], xA: x ∈ A then (THE y ∈ A. P.[y]) = x;
				apply ex1In_elim[OF ex1];
				- for z if zA: z ∈ A, Pz: P.[z], 1: ∀y ∈ A. P.[y] ⟹ y = z;
					note imp: 1[unfolded allIn_iff].
					have zT: (THE x ∈ A. P.[x]) = z;
						by imp TheIn_intro ex1 TheIn_in.
					unfold zT;
					by Px xA #unfold imp.
				.
			note TheIn_intro: TheIn_eq_intro[THEN eq.sym].
		end
	end

	theory Class:
		import Collect.
		assume Collect_eq_intro: if ∀x. P.[x] ⟺ Q.[x] then {x. P.[x]} = {x. Q.[x]}.
	begin
		lemma Collect_eq_iff: {x. P.[x]} = {x. Q.[x]} ⟺ (∀x. P.[x] ⟺ Q.[x]);
			apply iff_intro;
			- if eq;
				have in_iff: x ∈ {x. P.[x]} ⟺ x ∈ {x. Q.[x]};
					unfold eq.
				by in_iff[unfolded in_Collect_iff].
			by Collect_eq_intro[of P Q].
	end

	theory Propositional:
		fix Prop EQTYPE.
		import Propositional.
		import .Membership.
		assume eq_type: if A ∈ EQTYPE then (=) ∈ A → A → Prop.
	begin
		lemma eq_prop: if A: A ∈ EQTYPE, x: x ∈ A, y: y ∈ A then (x = y) ∈ Prop;
			by eq_type[OF A, THEN fun_elim1, THEN fun_elim1] x y.
	end

	theory FirstOrder:
		import Propositional.
		import FirstOrder.
		import Ex1In.
		assume ex1In_type: if A ∈ EQTYPE, ∀x ∈ A. P.[x] ∈ Prop then (∃!x ∈ A. P.[x]) ∈ Prop.
	begin
		interpret AllIn.
		interpret ExIn.
	end

	theory HigherOrder:
		import FirstOrder.
		import HigherOrder.
	begin
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

theory UnaryAbbreviation:
	---
	For any term with a free variable `x`,
	we assume one can introduce a symbol `f` such that `f x` is equal to the term.
	---
	assume abbrev: if ∀f. (∀x. f x = F.[x]) ⟹ P then P.
begin
	interpret Id;
		obtain id where id_eq: id x = x;
			- for thesis;
				apply abbrev[of (x. x)]>0.
			.
		.
	note(simp) id_eq.
	---
	One can obtain the type-free existential quantifier as a unary abbreviation.
	---
	interpret Ex;
		obtain (∃) where
			ex_intro1: for x P if P.[x] then ∃x. P.[x],
			ex_elim: if ∃x. P.[x], ∀x. P.[x] ⟹ Q then Q;
			- for thesis if assm;
				apply abbrev[of (P. (∀Q. (∀x. P.[x] ⟹ Q) ⟹ Q))];
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
	lemma ex_abbrev: ∃f. ∀x. f x = F.[x];
		apply ex_intro[OF abbrev].
	interpret Ex1;
		obtain (∃!) where
			ex1_intro1: for x P if P.[x], ∀y. P.[y] ⟹ y = x then ∃!x. P.[x],
			ex1_elim: if ∃!x. P.[x], ∀x. P.[x] ⟹ (∀y. P.[y] ⟹ y = x) ⟹ Q then Q;
			- for thesis if assm;
				apply abbrev[of (P. ∀Q. (∀x. P.[x] ⟹ (∀y. P.[y] ⟹ y = x) ⟹ Q) ⟹ Q)];
				- for (∃!) if eq;
					apply assm[of (∃!)];
					- for x P if Px, imp_eq;
						unfold eq;
						- for Q if imp;
							by imp[of x] Px imp_eq.
						.
					- for P if ex1;
						apply ex1[unfolded eq]=.
					.
				.
			.
		.
	obtain inj where
		inj_elim1: if inj f, f x = f y then x = y,
		inj_intro: if ∀x y. f x = f y ⟹ x = y then inj f;
		- for thesis if assm;
			apply abbrev[of (f. (∀x y. f x = f y ⟹ x = y))];
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
		by inj_intro.
	lemma inj_imp_ex1: if f: inj f then ∃!x'. f x' = f x;
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
				apply abbrev[of (y. THE z. f z = y)];
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

theory Pair: --- Syntactic Pairing ---
	fix (,) fst snd.
	assume fst(simp) fst (x,y) = x.
	assume snd(simp) snd (x,y) = y.
begin
	interpret pair: MetaInjective (,);
		- for x x' if eq: (,) x = (,) x' then x = x';
			have 1: fst (x,x) = fst (x',x);
				unfold eq.
			by 1[unfolded fst].
		.
	lemma pair_eq_pair_imp1: if eq: (x,y) = (x',y') then x = x';
		have 1: x = fst (x,y).
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

	theory UniqueChoice:
		import Ex1.
		assume unique_choice: if ∀x. ∃!y. P.[(x,y)] then ∃f. ∀x. P.[(x, f x)].
	end

end
