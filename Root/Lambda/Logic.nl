------
# Type-Free Logic on Lambda Calculus

On top fo untyped lambda calculus we define logical operations, and arrive at untyped multivalued intuitionistic logic.
------
begin

----
## Defining Logical Constructs
----
define true := ∀P. P ⟹ P.
define false := ∀P. P.
define[not] ¬ P := P ⟹ false.
define[and] P ∧ Q := ∀R. (P ⟹ Q ⟹ R) ⟹ R.
define[iff] P ⟺ Q := (P ⟹ Q) ∧ (Q ⟹ P).
define[or] P ∨ Q := ∀R. (P ⟹ R) ⟹ (Q ⟹ R) ⟹ R.
define[ex] (∃) α := ∀P. (∀x. α.[x] ⟹ P) ⟹ P.

define[neq] x ≠ y := ¬ x = y.

interpret TypeFreeIntuitionistic;
	retain false := false;
		if f: false;
			by f[unfolded false_def].
		.
	for P Q if !P, !Q then P ∧ Q;
		apply eq_imp_rev[OF and_def];
		for R if PQR: P ⟹ Q ⟹ R;
			by PQR.
		.
	for P Q if PQ: P ∧ Q then P;
		by eq_imp[OF and_def PQ].
	for P Q if PQ: P ∧ Q then Q;
		by eq_imp[OF and_def PQ].

	for P if nP: ¬P, !P then false;
		by nP[unfolded not_def].
	for P if nP: P ⟹ false then ¬P;
		by nP[folded not_def].

	for P Q if PQ: P ⟹ Q, QP: Q ⟹ P then P ⟺ Q;
		apply eq_imp_rev[OF iff_def];
		unfold and_def;
		for R if imp: (P ⟹ Q) ⟹ (Q ⟹ P) ⟹ R;
			by imp[OF PQ QP].
		.
	for P Q if PQ: P ⟺ Q then P ⟹ Q;
		apply PQ[unfolded iff_def and_def];
		if PQ: P ⟹ Q;
			by PQ.
		.
	for P Q if PQ: P ⟺ Q then Q ⟹ P;
		apply PQ[unfolded iff_def and_def];
		if PQ: P ⟹ Q, QP: Q ⟹ P;
			by QP.
		.

	for P Q if P: P then P ∨ Q;
		have 1: if PR: P ⟹ R, QR: Q ⟹ R then R;
			by PR[OF P].
		by eq_imp_rev[OF or_def 1].
	for P Q if Q: Q then P ∨ Q;
		have 1: if PR: P ⟹ R, QR: Q ⟹ R then R;
			by QR[OF Q].
		by eq_imp_rev[OF or_def 1].
	for P Q, P ∨ Q ⟹ (∀R. (P ⟹ R) ⟹ (Q ⟹ R) ⟹ R);
		unfold or_def;
		apply imp.refl=.

	for x α if ax: α.[x] then ∃x. α.[x];
		unfold ex_def;
		for P if all: ∀x. α.[x] ⟹ P;
			by all[OF ax].
		.
	for α, (∃x. α.[x]) ⟹ ∀P. (∀x. α.[x] ⟹ P) ⟹ P;
		unfold ex_def;
		apply imp.refl=.
	retain true := true;
		unfold true_def.
	.

---
Without extensionality, equality is not congruent with respect to binding.
So rewriting by (⟺) is actually more essential.
---

set rewrite! iff_elim1 iff_elim2 iff.refl iff.trans.
set dual iff.sym.

lemma eq_imp_iff#cong: if PQ: P = Q then P ⟺ Q;
	unfold(=) PQ.

interpret eq_iff: MetaCommutative (=) (⟺);
	for x y, x = y ⟺ y = x;
		apply iff_intro;
		if xy: x = y;
			unfold xy.
		if yx: y = x;
			unfold yx.
		.
	.

theorem russel_paradox: ¬(∀P. P ∨ ¬P);
	apply not_intro;
	if or: ∀P. P ∨ ¬P;
		define R x := ¬ x x.
		have eq: R R = (¬ R R);
			by R_def.
		have Ror: R R ∨ ¬ R R;
			by or.
		apply or_elim[OF Ror];
		if RR: R R;
			have nRR: ¬ R R;
				fold(=) eq;
				by RR.
			by not_imp_false[OF nRR RR].
		if nRR: ¬ R R;
			have RR: R R;
				unfold eq;
				by nRR.
			by not_imp_false[OF nRR RR].
		.
	.

theory If:
	fix (if) (then) (else).
	assume if: P ⟹ (if P then t else e) = t.
	assume if_not: ¬P ⟹ (if P then t else e) = e.
end

theory Choice:
	assume choice: (∀x. ∃y. P x y) ⟹ ∃f. ∀x. P x (f x).
end

theory ChoiceOperator:
	fix (SOME).
	assume ex_imp_SOME: (∃x. P.[x]) ⟹ P.[SOME x. P.[y]].
end

theory Collect:
	fix (:) Collect.
	assume in_Collect_iff: x : Collect P ⟺ P x.
end

-- TODO: should have mutual obtain
define [in] x : σ := σ x.
define Collect P := P.

interpret Collect;
	by #unfold in_def Collect_def.

define[empty] ∅ := Collect (λx. false).

define Singleton x := Collect (λy. y = x).

define[cup] X ∪ Y := Collect (λx. x : X ∨ x : Y).

set set_comprehension Collect (λ) ∅ Singleton (∪).

define decided := {x. x ∨ ¬x}.

lemma in_decided_iff: P : decided ⟺ P ∨ ¬P;
	unfold decided_def;
	unfold in_Collect_iff;
	unfold beta.

interpret decided: ..ClassicalPL;
	instantiate prop := decided.
	show: true : decided;
		by or_intro #unfold in_decided_iff.
	show: false : decided;
		by or_intro not_false #unfold in_decided_iff.
	show imp_type: for x y if x: x : decided, y: y : decided then (x ⟹ y) : decided;
		unfold in_decided_iff;
		apply or_elim[OF y[unfolded in_decided_iff]];
		- by or_intro1.
		if ny: ¬y;
			apply or_elim[OF x[unfolded in_decided_iff]];
			if !x;
				apply+ or_intro2 not_intro;
				by not_imp_false[OF ny].
			if nx: ¬x;
				apply or_intro1[OF not_elim[OF nx]].
			.
		.
	for x, x : decided ⟹ (¬ x) : decided;
		unfold+ in_decided_iff;
		by or_intro nnot_intro #elim or_elim.
	show and_type: for x y, x : decided ⟹ y : decided ⟹ (x ∧ y) : decided;
		unfold+ in_decided_iff;
		if x: x ∨ ¬x, y: y ∨ ¬y;
			apply or_elim[OF x];
			if !x;
				apply or_elim[OF y];
				- by or_intro1 and_intro.
				by or_intro2 nand_intro2.
			by or_intro2 nand_intro1.
		.
	for x y, x : decided ⟹ y : decided ⟹ (x ∨ y) : decided;
		unfold+ in_decided_iff;
		if x: x ∨ ¬x, y: y ∨ ¬y;
			apply or_elim[OF x];
			- by or_intro1.
			if ! ¬x;
				apply or_elim[OF y];
				if ! y;
					apply or_intro1;
					by or_intro2.
				if ! ¬y;
					apply or_intro2;
					unfold nor_iff;
					by and_intro.
				.
			.
		.
	for x y, x : decided ⟹ y : decided ⟹ (x ⟺ y) : decided;
		unfold iff_def;
		by and_type imp_type.
	- .
	- by not_intro.
	note! and_intro.
	note! or_intro.
	note! iff_intro.
	note #elim: not_imp_false.
	note #elim: and_elim.
	note #elim: or_elim.
	note #elim: iff_elim.
	note #elim: false_elim.
	show: if P : decided then P ∨ ¬ P;
		by #unfold in_decided_iff.
	.

thm decided.pierce_law.

lemma nnot_decided: ¬ ¬ x : decided;
	unfold in_decided_iff;
	by nnot_excluded_middle.



define [fun] (σ → τ) := {f. ∀x. x : σ ⟹ f x : τ}.

interpret FunType;
	for f σ τ if f: f : σ → τ then ∀a. a : σ ⟹ f a : τ;
		by f[unfolded fun_def in_Collect_iff beta].
	for f σ τ if assm: ∀x. x : σ ⟹ f x : τ then f : σ → τ;
		unfold fun_def in_Collect_iff beta;
		by assm.
	.

define UNIV := {x. true}.

lemma in_UNIV! x : UNIV;
	unfold UNIV_def in_Collect_iff beta.

define[tall] (∀:) ι α := ∀x. x : ι ⟹ α.[x].
define[tex] (∃:) ι α := ∀P. (∀x. α.[x] ⟹ x : ι ⟹ P) ⟹ P.

interpret intuitionistic: ..IntuitionisticFOL;
	instantiate prop := UNIV.
	- .
	- .
	- by #unfold tall_def.
	for x ι α if tall: ∀y:ι. α.[y];
		by tall[unfolded tall_def].
	retain true.
	retain false;
		by #elim false_elim.
	show! ∀P. (P ⟹ false) ⟹ P : UNIV ⟹ ¬ P;
		by not_intro.
	for P, ¬ P ⟹ P ⟹ P : UNIV ⟹ false;
		by not_imp_false[of P].
	- by and_intro.
	- by #elim and_elim.
	- by #elim and_elim.
	- by or_intro.
	- by or_intro.
	- by #elim or_elim.
	- by iff_intro.
	- by #elim iff_elim.
	- by #elim iff_elim.
	for x α ι if !α.[x], !x : ι, foo;
		unfold tex_def;
		for P if all: ∀z. α.[z] ⟹ z : ι ⟹ P;
			by all[of x].
		.
	for ι α if ex: ∃x:ι. α.[x];
		for P if imp: ∀x. α.[x] ⟹ x : ι ⟹ P;
			apply ex[unfolded tex_def];
			for x;
				by imp[of x].
			.
		.
	.

lemma neq_intro: if xyf: x = y ⟹ false then x ≠ y;
	unfold neq_def;
	apply not_intro;
	by xyf.

note neq_elim: eq_imp[OF neq_def].

lemma neq_irrefl: ¬ x ≠ x;
	unfold neq_def;
	apply nnot_intro.

lemma neq_imp_false: if neq: x ≠ y, eq: x = y then false;
	by not_imp_false[OF neq[unfolded neq_def] eq].

lemma neq_refl_imp_false: if xx: x ≠ x then false;
	by neq_imp_false[OF xx eq.refl].

lemma true_neq_false: true ≠ false;
	apply neq_intro;
	if tf: true = false then false;
		fold tf.
	.

---
### Unique Existence
---

binder ∃! 0 0.

define[ex1] (∃!) α := ∃x. α.[x] ∧ (∀y. α.[y] ⟹ x = y).

lemma ex1_intro: for x if x: α.[x], 1: ∀y. α.[y] ⟹ x = y then ∃!x. α.[x];
	unfold ex1_def;
	apply ex_intro1[of x];
	apply and_intro;
	by x 1.

lemma ex1_elim:
	if ex1: ∃!x. α.[x], body: ∀x. α.[x] ⟹ (∀y. α.[y] ⟹ x = y) ⟹ P
	then P;
	obtain x where and: (α.[x]) ∧ (∀y. α.[y] ⟹ x = y);
		for thesis;
			apply ex1[unfolded+ ex1_def ex_def, of thesis]=.
		.
	have ax: α.[x];
		by and_elim1[OF and].
	have 1: ∀y. α.[y] ⟹ x = y;
		by and_elim2[OF and].
	by body[OF ax 1].

theory UniqueChoice:
	fix (THE).
	assume ex1_imp_THE: (∃!x. P.[x]) ⟹ P.[THE x. P.[x]].
begin
	lemma ex1_imp_THE_eq: if ex1: ∃!y. P.[y], x: P.[x] then (THE y. P.[y]) = x;
		apply ex1_elim[OF ex1];
		for z if az: P.[z], 1: ∀y. P.[y] ⟹ z = y;
			have zx: z = x;
				by 1[OF x].
			have zT: z = (THE x. P.[x]);
				by 1[OF ex1_imp_THE[OF ex1]].
			by zx[unfolded zT].
		.
end

end


