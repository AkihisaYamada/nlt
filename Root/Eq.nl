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
	lemma eq_imp_iff(cong) if eq: P = Q then P ⟺ Q;
		by iff_intro #unfold(=) eq.
end

theory Const:
	fix Const const const_fun const_arg.
	assume const_Const: const Const.
	assume const_app: if const c then const (c x).
	assume const_fun: if const c then const_fun (c x) = c.
	assume const_arg: if const c then const_arg (c x) = x.
begin
	lemma const_eq_fun: if ! const c, ! const d, cd: c x = d y then c = d;
		have 1: const_fun (c x) = const_fun (d y);
			unfold cd.
	by 1[unfolded const_fun].

	lemma const_eq_arg: if ! const c, ! const d, cd: c x = d y then x = y;
		have 1: const_arg (c x) = const_arg (d y);
			unfold cd.
	by 1[unfolded const_arg].

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
	fix If (,).
	assume If_then: if P then If P (x,y) = x.
	---
	A minimal specification: P and ¬P will not lead to explosion.
	---
	assume If_else: if P ⟹ x = y then If P (x,y) = y.
begin
	interpret Pair;
		obtain fst where fst: fst (x,y) = x;
			- for thesis if assm;
				apply assm[of (If (∀P. P ⟹ P))];
				by If_then.
			.
		obtain snd where snd: snd (x,y) = y;
			- for thesis if assm;
				apply assm[of (If (∀P. P))];
				by If_else.
			.
		-; by fst.
		-; by snd.
		.
end

theory UnaryAbbreviation:
	---
	For any term with a free variable `x`,
	we assume one can introduce a symbol `f` such that `f x` is equal to the term.
	---
	assume abbrev: if ∀f. (∀x. f x = F.[x]) ⟹ thesis then thesis.
begin
	---
	One can obtain the type-free existential quantifier as a unary abbreviation.
	---
	interpret Ex;
		obtain (∃) where
			ex_intro1: ∀x P. P.[x] ⟹ ∃x. P.[x],
			ex_elim: (∃x. P.[x]) ⟹ ∀Q. (∀x. P.[x] ⟹ Q) ⟹ Q;
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
	obtain id where id: id x = x;
		- for thesis if assm;
			apply abbrev[of (x. x)];
			- for id if eq;
				apply assm[of id];
				by #unfold eq.
			.
		.
	note(unfold) id.
	obtain (∃!) where
		ex1_intro1: ∀x P. P.[x] ⟹ (∀y. P.[y] ⟹ y = x) ⟹ ∃!x. P.[x],
		ex1_elim: (∃!x. P.[x]) ⟹ ∀Q. (∀x. P.[x] ⟹ (∀y. P.[y] ⟹ y = x) ⟹ Q) ⟹ Q;
		- for thesis if assm;
			apply abbrev[of (P. ∀Q. (∀x. P.[x] ⟹ (∀y. P.[y] ⟹ y = x) ⟹ Q) ⟹ Q)];
			- for (∃!) if eq: ∀P. (∃!) P = (∀Q. (∀x. P.[x] ⟹ (∀y. P.[y] ⟹ y = x) ⟹ Q) ⟹ Q);
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
	lemma ex1_intro: if assm: ∀Q. (∀x. P.[x] ⟹ (∀y. P.[y] ⟹ y = x) ⟹ Q) ⟹ Q then ∃!x. P.[x];
		apply assm;
		- for x if Px;
			by ex1_intro1[OF Px].
		.
	lemma ex1_imp_ex: if ex1: ∃!x. P.[x] then ∃x. P.[x];
		apply ex_intro;
		- for Q if assm;
			apply ex1_elim[OF ex1];
			- for x;
				by assm[of x].
			.
		.
	obtain inj where
		inj_elim1: inj f ⟹ ∀x y. f x = f y ⟹ x = y,
		inj_intro: (∀x y. f x = f y ⟹ x = y) ⟹ inj f;
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
	theory UniqueChoiceOp:
		fix (THE).
		assume ex1_imp_THE: (∃!x. P.[x]) ⟹ P.[THE x. P.[x]].
	begin
		lemma ex1_imp_THE_eq: if ex1: ∃!y. P.[y], Px: P.[x] then (THE y. P.[y]) = x;
			apply ex1_elim[OF ex1];
			- for z if Pz: P.[z], 1: ∀y. P.[y] ⟹ y = z;
				have zT: (THE x. P.[x]) = z;
					by 1[OF ex1_imp_THE[OF ex1]].
				unfold zT;
				unfold 1[OF Px].
			.
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
	end
end

theory Abbreviation:
	--- To allow for binary abstraction and more, we assume pairs and Currying. ---
	import UnaryAbbreviation.
	import Pair.
	assume curry: ∀f. ∃f'. ∀x y. f' x y = f (x,y).
begin
	--- Here one can obtain type-free binary logical operators as abbreviations. ---
	interpret Iff;
		obtain (⟺) where
			iff_intro: (P ⟹ Q) ⟹ (Q ⟹ P) ⟹ (P ⟺ Q),
			iff_elim1: (P ⟺ Q) ⟹ P ⟹ Q,
			iff_elim2: (P ⟺ Q) ⟹ Q ⟹ P;
			- for thesis if assm;
				apply abbrev[of (p. ∀R. ((fst p ⟹ snd p) ⟹ (snd p ⟹ fst p) ⟹ R) ⟹ R)];
				- for f if f;
					apply ex_elim[OF curry[of f]];
					- for g if g;
						apply assm[of g];
						- for P Q if PQ, QP;
							unfold g f;
							- for R if body;
								apply body[unfolded fst snd];
								-; by PQ.
								-; by QP.
								.
							.
						- for P Q if gPQ, P;
							apply gPQ[unfolded g f];
							unfold fst snd;
							- if PQ, QP;
								by PQ[OF P].
							.
						- for P Q if gPQ, Q;
							apply gPQ[unfolded g f];
							unfold fst snd;
							- if PQ, QP;
								by QP[OF Q].
							.
						.
					.
				.
			.
		.
	interpret Intuitionistic;
		obtain true where true_intro: true;
			- for thesis if assm;
				apply assm[of (∀P. P ⟹ P)].
			.
		obtain false where false_elim: false ⟹ ∀P. P;
			- for thesis if assm;
				apply assm[of (∀P. P)].
			.
		obtain (∧) where
			and_intro: P ⟹ Q ⟹ P ∧ Q,
			and_elim1: P ∧ Q ⟹ P,
			and_elim2: P ∧ Q ⟹ Q;
			- for thesis if assm;
				apply abbrev[of (p. ∀R. (fst p ⟹ snd p ⟹ R) ⟹ R)];
				- for f if f;
					apply ex_elim[OF curry[of f]];
					- for f' if f';
						apply assm[of f', unfolded f' f fst snd].
					.
				.
			.
		obtain (∨) where
			or_intro1: ∀P Q. P ⟹ P ∨ Q,
			or_intro2: ∀P Q. Q ⟹ P ∨ Q,
			or_elim: P ∨ Q ⟹ ∀R. (P ⟹ R) ⟹ (Q ⟹ R) ⟹ R;
			- for thesis if assm;
				apply abbrev[of (p. ∀R. (fst p ⟹ R) ⟹ (snd p ⟹ R) ⟹ R)];
				- for f if f;
					apply ex_elim[OF curry[of f]];
					- for f' if f';
						apply assm[of f', unfolded f' f fst snd];
						-; by #unfold imp_imp_iff.
						-; by #unfold imp_imp_iff.
						- for P Q; apply imp.refl=.
						.
					.
				.
			.
		obtain (¬) where
			not_intro: (P ⟹ false) ⟹ ¬P,
			not_imp_false: ¬P ⟹ P ⟹ false;
			- for thesis if assm;
				apply abbrev[of (P. P ⟹ false)];
				- for f if f;
					apply assm[of f, unfolded f].
				.
			.
		.
	obtain inverts where
		inverts_intro: (∀x. f (g x) = x) ⟹ inverts f g,
		inverts_elim1: inverts f g ⟹ ∀x. f (g x) = x;
		- for thesis if assm;
			apply abbrev[of (p. ∀x. fst p (snd p x) = x)];
			- for inv if inv;
				apply ex_elim[OF curry[of inv]];
				- for inverts if inverts;
					apply assm[of inverts, unfolded inverts inv fst snd].
				.
			.
		.
end

theory Notation:
	import Abbreviation.
	import UniqueChoiceOp.
begin
print.
thy.
	interpret Collect;
		obtain Collect where Collect_inj: inj Collect;
			- for thesis;
				apply ex_elim[OF ex_inj]=.
			.
		obtain (∋) where inv: (∋) (Collect P) = P;
			- for thesis;
				apply Collect_inj[THEN inj_imp_ex_inv, THEN ex_elim]=.
			.
		obtain (∈) where
			Collect_intro: P x ⟹ x ∈ Collect P,
			Collect_elim1: x ∈ Collect P ⟹ P x;
			- for thesis if assm;
				apply abbrev[of (p. snd p ∋ fst p)];
				- for in if in;
					apply curry[of in, THEN ex_elim];
thm eq_imp_iff.
					unfold(⟺) in;
e

	obtain Collect where 

	interpret Membership:
		obtain (∈) where 

end


theory Membership:
	import Membership.
begin
	theory Image:
		fix (`).
		assume image_intro: if x ∈ A then f x ∈ f ` A.
		assume image_elim: if y ∈ f ` A then for P if ∀x. y = f x ⟹ x ∈ A ⟹ P then P.
	end
end

theory Classes:
	import Classes.
begin
	theory Prod:
		fix (×).
		import Pair.
		assume pair_type: (,) : X → Y → X × Y.
	end
end

theory Ext:
	assume ext: if ∀x ∈ A. f x = g x, A ∈ EQTYPE, B ∈ EQTYPE, f ∈ A → B, g ∈ A → B
	then f = g.
end
