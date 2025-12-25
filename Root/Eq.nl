---
# Equality
---

import Base.

fix (=).

assume eq_refl! x = x.
assume eq_imp_meta: for X, if y = z, X.[y] then X.[z].

begin -- Above are the all axioms.

interpret MetaMagmas (=).

namespace eq begin

	interpret MetaEquivalence (=);
		for x y if xy: x = y then y = x;
			by eq_imp_meta[of (z. z = x), OF xy].
		for x y z if xy: x = y, yz: y = z then x = z;
			by eq_imp_meta[of (w. x = w), OF yz xy].
	.

end

lemma eq_imp: if PQ: P = Q, P: P then Q;
by eq_imp_meta[of (x. x), OF PQ P].

lemma eq_imp_rev: if PQ: P = Q, Q: Q then P;
by eq_imp[OF eq.sym[OF PQ] Q].

set rewrite eq_imp eq_imp_rev eq.refl eq.trans.
set dual eq.sym.

lemma eq_cong_meta: for α if xy: x = y then α.[x] = α.[y];
by eq_imp_meta[of (z. α.[x] = α.[z]), OF xy eq.refl].

lemma arg_cong: if xy: x = y then f x = f y;
by eq_cong_meta[of (z. f z), OF xy].

lemma fun_cong: if fg: f = g then f x = g x;
by eq_cong_meta[of (h. h x), OF fg].

lemma eq_cong(cong) for f x if fg: f = g, xy: x = y then f x = g y;
	have 1: f x = f y;
		by arg_cong[OF xy].
	have 2: f y = g y;
		by fun_cong[OF fg].
by eq.trans[OF 1 2].

theory UnaryAbbreviation:
---
For any term `F.[x]` with a free variable `x`,
we assume one can introduce a symbol `f` such that `f x = F.[x]`.
---
	assume abbrev: for F thesis if ∀f. (∀x. f x = F.[x]) ⟹ thesis then thesis.
begin

---
One can obtain the type-free existential quantifier as a unary abbreviation.
---
	obtain (∃) where
		ex_intro: P.[x] ⟹ ∃x. P.[x],
		ex_elim: (∃x. P.[x]) ⟹ ∀thesis. (∀x. P.[x] ⟹ thesis) ⟹ thesis
	;	for thesis if assm;
			apply abbrev[of (P. (∀Q. (∀x. P.[x] ⟹ Q) ⟹ Q))];
			for (∃) if eq: ∀P. (∃) P = (∀ Q. (∀x. P.[x] ⟹ Q) ⟹ Q);
				apply assm[of (∃)];
				for P x if Px: P.[x] then ∃x. P.[x];
					unfold eq;
					for Q if imp: ∀x. P.[x] ⟹ Q then Q;
						by imp[OF Px].
				.
				for P if ex: ∃x. P.[x];
					for Q if imp: ∀x. P.[x] ⟹ Q then Q;
						apply ex[unfolded eq];
					by #elim imp.
				.
			.
		.
	.

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
		for thesis if assm;
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
		for x x' if eq: f x = f x';
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
		for x x' if eq: (,) x = (,) x' then x = x';
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

theory Abbreviation:
	--- In addition to unary abstraction, we assume Currying. ---
	import UnaryAbbreviation.
	import Pair.
	assume curry: for f, ∃f'. ∀x y. f' x y = f (x,y).
begin
print.
	--- Here one can obtain type-free binary logical operators as abbreviations. ---
	namespace iff begin
		obtain (⟺) where
			intro: (P ⟹ Q) ⟹ (Q ⟹ P) ⟹ (P ⟺ Q),
			elim1: (P ⟺ Q) ⟹ P ⟹ Q,
			elim2: (P ⟺ Q) ⟹ Q ⟹ P
		;	for thesis if assm;
				apply abbrev[of (p. ∀R. ((fst p ⟹ snd p) ⟹ (snd p ⟹ fst p) ⟹ R) ⟹ R)];
				for f if f;
					apply ex_elim[OF curry[of f]];
					for g if g;
						apply assm[of g];
						for P Q if PQ, QP;
							unfold g f;
							for R if body;
								apply body[unfolded fst snd];
								- by PQ.
								- by QP.
							.
						.
						for P Q if gPQ, P;
							apply gPQ[unfolded g f];
							unfold fst snd;
							if PQ, QP;
								by PQ[OF P].
						.
						for P Q if gPQ, Q;
							apply gPQ[unfolded g f];
							unfold fst snd;
							if PQ, QP;
								by QP[OF Q].
						.
					.
				.
			.
		.
		lemma elim:
			if PQ: P ⟺ Q then for R if imp: (P ⟹ Q) ⟹ (Q ⟹ P) ⟹ R then R;
		by imp elim1[OF PQ] elim2[OF PQ].

		interpret MetaEquivalence (⟺);
			- by intro.
			- by intro #elim elim.
			for P Q R if PQ: P ⟺ Q, QR: Q ⟺ R then P ⟺ R;
				apply intro;
				- by elim1[OF QR] elim1[OF PQ].
				- by elim2[OF PQ] elim2[OF QR].
			.
		.

		interpret MetaMagmas (⟺).

		lemma cong_imp: for P R if PQ: P ⟺ Q, RS: R ⟺ S then (P ⟹ R) ⟺ (Q ⟹ S);
			apply intro;
			if PR: P ⟹ R, !Q then S;
				by elim1[OF RS] PR elim2[OF PQ].
			if QS: Q ⟹ S, !P then R;
				by elim2[OF RS] QS elim1[OF PQ].
		.

		lemma cong_iff: for P R if PQ: P ⟺ Q, RS: R ⟺ S then (P ⟺ R) ⟺ (Q ⟺ S);
			apply intro;
			if PR: P ⟺ R then Q ⟺ S;
				have QR: Q ⟺ R;
				by trans[OF sym[OF PQ] PR].
			by trans[OF QR RS].
			if QS: Q ⟺ S then P ⟺ R;
				have PS: P ⟺ S;
				by trans[OF PQ QS].
			by trans[OF PS sym[OF RS]].
		.

		lemma cong_all: if ab: ∀x. α.[x] ⟺ β.[x] then (∀x. α.[x]) ⟺ (∀x. β.[x]);
			apply intro;
			if ! ∀x. α.[x] then ∀x. β.[x];
				by elim1[OF ab].
			if ! ∀x. β.[x] then ∀x. α.[x];
				by elim2[OF ab].
		.

	end

	set rewrite! iff.elim1 iff.elim2 iff.refl iff.trans.
	set dual iff.sym.

	note(cong) iff.cong_imp iff.cong_iff iff.cong_all.

	obtain (∧) where
		and_intro: P ⟹ Q ⟹ P ∧ Q,
		and_elim1: P ∧ Q ⟹ P,
		and_elim2: P ∧ Q ⟹ Q
	;	for thesis if assm;
			obtain f where f: f p = (∀R. (fst p ⟹ snd p ⟹ R) ⟹ R);
			for thesis2 if assm2;
				apply abbrev[of (p. ∀R. (fst p ⟹ snd p ⟹ R) ⟹ R)];
					for f if eq;
					by assm2[of f] eq.
				.
			.
			apply ex_elim[OF curry[of f]];
			for (∧) if and;
				apply assm[of (∧)];
				for P Q if P: P, Q: Q then P ∧ Q;
					unfold and f;
					for R if PQR;
						by PQR[unfolded fst snd] P Q.
				.
				for P Q if PQ;
					apply PQ[unfolded and f];
					if P, Q;
						by P[unfolded fst].
				.
				for P Q if PQ;
					apply PQ[unfolded and f];
					if P, Q;
						by Q[unfolded snd].
				.
			.
		.
	.

end



theory Ext:
	assume ext: if ∀x ∈ A. f x = g x, A ∈ TYPE, B ∈ TYPE, f ∈ A → B, g ∈ A → B
	then f = g.
end
