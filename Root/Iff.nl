---
# If-and-only-if
---

import Base.
fix (⟺).

assume iff_intro: if P ⟹ Q, Q ⟹ P then P ⟺ Q.
assume iff_elim1: if P ⟺ Q, P then Q.
assume iff_elim2: if P ⟺ Q, Q then P.

begin

lemma iff_elim: if PQ: P ⟺ Q, imp: (P ⟹ Q) ⟹ (Q ⟹ P) ⟹ R then R;
	by imp iff_elim1[OF PQ] iff_elim2[OF PQ].

-- We can think of meta-magmas with respect to ⟺
interpret iff: MetaMagmas (⟺).

interpret iff: MetaEquivalence (⟺);
	- by iff_intro.
	- by iff_intro #elim iff_elim.
	- if PQ: P ⟺ Q, QR: Q ⟺ R then P ⟺ R;
		apply iff_intro;
		- by iff_elim1[OF QR] iff_elim1[OF PQ].
		- by iff_elim2[OF PQ] iff_elim2[OF QR].
		.
	.

note! iff.refl.

set rewrite iff_elim1 iff_elim2 iff.refl iff.trans.
set dual iff.sym.

interpret iff: iff.MetaCompatible (⟺);
	- if PQ: P ⟺ Q, RS: R ⟺ S then (P ⟺ R) ⟺ (Q ⟺ S);
		apply iff_intro;
		- if PR: P ⟺ R then Q ⟺ S;
			have QR: Q ⟺ R;
				by iff.trans[OF iff.sym[OF PQ] PR].
			by iff.trans[OF QR RS].
		- if QS: Q ⟺ S then P ⟺ R;
			have PS: P ⟺ S;
				by iff.trans[OF PQ QS].
			by iff.trans[OF PS iff.sym[OF RS]].
		.
	.

note(cong) iff.cong.

interpret iff: iff.MetaCommutative (⟺);
	by iff_intro[OF iff.sym iff.sym].

interpret imp: iff.MetaCompatible (⟹);
	- if PQ: P ⟺ Q, RS: R ⟺ S then (P ⟹ R) ⟺ (Q ⟹ S);
		apply iff_intro;
		- if PR: P ⟹ R, !Q then S;
			by iff_elim1[OF RS] PR iff_elim2[OF PQ].
		- if QS: Q ⟹ S, !P then R;
			by iff_elim2[OF RS] QS iff_elim1[OF PQ].
		.
	.

lemma imp_cong(cong) if PQ: P ⟺ Q, RS: Q ⟹ R ⟺ S then (P ⟹ R) ⟺ (Q ⟹ S);
	apply iff_intro;
	- if PR, Q;
		note P: Q[folded PQ].
		note R: PR[OF P].
		by R[unfolded RS[OF Q]].
	- if QS, P;
		note Q: P[unfolded PQ].
		note S: QS[OF Q].
		by S[folded RS[OF Q]].
	.

lemma all_cong(cong) if PQ: ∀x. P.[x] ⟺ Q.[x] then (∀x. P.[x]) ⟺ (∀x. Q.[x]);
	apply iff_intro;
	- if ! ∀x. P.[x] then ∀x. Q.[x];
		by iff_elim1[OF PQ].
	- if ! ∀x. Q.[x] then ∀x. P.[x];
		by iff_elim2[OF PQ].
	.

lemma imp_imp_iff: if !P then (P ⟹ Q) ⟺ Q;
	by iff_intro.

lemma imp_iff_iff: if !P then (P ⟺ Q) ⟺ Q;
	by iff_intro #elim iff_elim.

lemma all_imp2_iff: (∀Q. (P ⟹ Q) ⟹ Q) ⟺ P;
	by iff_intro.

lemma imp3_iff: (((P ⟹ Q) ⟹ Q) ⟹ Q) ⟺ (P ⟹ Q);
	apply iff_intro[OF imp2_imp_imp];
	- if PQ: P ⟹ Q, PQQ: (P ⟹ Q) ⟹ Q then Q;
		by PQQ[OF PQ].
	.

lemma all_indep(simp) (∀x. P) ⟺ P;
	by iff_intro.

lemma imp_all_iff: (P ⟹ ∀x. Q.[x]) ⟺ (∀x. P ⟹ Q.[x]);
	apply iff_intro;
	- if imp; by imp.
	- if imp; by imp.
	.

lemma imp_iff_iff1: if !P then (P ⟺ Q) ⟺ Q;
	by iff_intro #elim iff_elim.

---
## Deriving Conjunction
---
theory And:
	fix (∧).
	assume and_iff: P ∧ Q ⟺ (∀R. (P ⟹ Q ⟹ R) ⟹ R).
begin
	interpret And;
		by #unfold and_iff.
	interpret and: iff.MetaCompatible (∧);
		- if P: P ⟺ P', Q: Q ⟺ Q' then P ∧ Q ⟺ P' ∧ Q';
			by iff_intro #unfold P Q.
		.
	note(cong) and.cong.
	interpret and: iff.MetaIdempotent (∧);
		by iff_intro.
	interpret and: iff.MetaCommutative (∧);
		by iff_intro.
	interpret and: iff.MetaAssociative (∧);
		by iff_intro.
	lemma and_cong1: if P: P ⟺ P', Q: P' ⟹ Q ⟺ Q' then P ∧ Q ⟺ P' ∧ Q';
		by iff_intro #unfold P Q.
	lemma and_imp_iff_imp_imp(simp) (P ∧ Q ⟹ R) ⟺ (P ⟹ Q ⟹ R);
		by iff_intro.
	lemma imp_and_iff1: if P: P then P ∧ Q ⟺ Q;
		by iff_intro P.
	lemma imp_and_iff2: if Q: Q then P ∧ Q ⟺ P;
		by iff_intro Q.
	lemma iff_iff_and: (P ⟺ Q) ⟺ (P ⟹ Q) ∧ (Q ⟹ P);
		by iff_intro #elim iff_elim.
	lemma imp_and_distrib: (P ⟹ Q ∧ R) ⟺ (P ⟹ Q) ∧ (P ⟹ R);
		apply iff_intro;
		- if imp;
			apply and_intro;
			- if P;
				apply and_elim[OF imp[OF P]].
			- if P;
				apply and_elim[OF imp[OF P]].
			.
		.
	lemma all_and_distrib: (∀x. P.[x] ∧ Q.[x]) ⟺ (∀x. P.[x]) ∧ (∀x. Q.[x]);
		apply iff_intro;
		- if ab: ∀x. P.[x] ∧ Q.[x];
			apply and_intro;
			- for x;
				by and_elim1[OF ab].
			- for x;
				by and_elim2[OF ab].
			.
		.
end

---
## Deriving Restricted Quantifiers via `(⟺)`
---
theory AllRel:
	fix (<) (∀<).
	assume all_def: (∀x < a. P.[x]) ⟺ (∀x. x < a ⟹ P.[x]).
begin
	interpret AllRel;
		- if all: ∀x. x < a ⟹ P.[x] then ∀x < a. P.[x];
			by all[folded all_def].
		- if allIn: ∀x < a. P.[x], x: x < a then P.[x];
			by allIn[unfolded all_def, OF x].
		.
	lemma all_cong_strong:
		if a: ∀x. x < a ⟺ x < a', P: ∀x. x < a' ⟹ (P.[x] ⟺ P'.[x])
		then (∀x < a. P.[x]) ⟺ (∀x < a'. P'.[x]);
		unfold+ all_def a P.
	lemma all_cong_weak:
		if P: ∀x. x < a ⟹ (P.[x] ⟺ P'.[x]) then (∀x < a. P.[x]) ⟺ (∀x < a. P'.[x]);
		unfold+ all_def P.
end

theory ExRel:
	fix (<) (∃<).
	assume ex_def: (∃x < a. P.[x]) ⟺ (∀Q. (∀x. x < a ⟹ P.[x] ⟹ Q) ⟹ Q).
begin
	interpret ExRel;
		- if x: x < a, Px: P.[x] then ∃x < a. P.[x];
			unfold ex_def;
			- for thesis if assm;
				apply assm[of x];
				by x Px.
			.
		- if ex: ∃x < a. P.[x], imp: ∀x. x < a ⟹ P.[x] ⟹ Q then Q;
			apply ex[unfolded ex_def];
			- for x;
				by imp[of x].
			.
		.
	lemma ex_cong_strong:
		if a: ∀x. x < a ⟺ x < a', P: ∀x. x < a' ⟹ (P.[x] ⟺ P'.[x])
		then (∃x < a. P.[x]) ⟺ (∃x < a'. P'.[x]);
		unfold+ ex_def a P.
	lemma ex_cong_weak:
		if P: ∀x. x < a ⟹ (P.[x] ⟺ P'.[x]) then (∃x < a. P.[x]) ⟺ (∃x < a. P'.[x]);
		unfold+ ex_def P.
	lemma ex_imp_iff: ((∃x < a. P.[x]) ⟹ Q) ⟺ (∀x. x < a ⟹ P.[x] ⟹ Q);
		apply iff_intro;
		- if imp, x: x < a, Px: P.[x];
			apply imp ex_intro1[OF x Px].
		- if all, ex;
			apply ex_elim[OF ex];
			- for x if x, Px;
				apply all[OF x Px].
			.
		.
end
