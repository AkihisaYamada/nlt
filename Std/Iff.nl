---
# Type-free if-and-only-if
---
fix (⟺).

assume iff_intro: if P ⟹ Q, Q ⟹ P then P ⟺ Q.
assume iff_elim1#rewrite_imp if P ⟺ Q, P then Q.
assume iff_elim2#rewrite_rev if P ⟺ Q, Q then P.

begin

set simp (⟺).
set rule (⟺).

lemma iff_elim: if PQ: P ⟺ Q, imp: (P ⟹ Q) ⟹ (Q ⟹ P) ⟹ R then R;
	by imp iff_elim1[OF PQ] iff_elim2[OF PQ].

-- We can think of meta-magmas with respect to ⟺
interpret iff: MetaRelation (⟺).
interpret iff: MetaEquivalence (⟺);
	- by iff_intro.
	- by iff_intro #elim iff_elim.
	- if PQ: P ⟺ Q, QR: Q ⟺ R then P ⟺ R;
		apply iff_intro;
		- by iff_elim1[OF QR] iff_elim1[OF PQ].
		- by iff_elim2[OF PQ] iff_elim2[OF QR].
		.
	.
note#intro#refl iff.refl.
note#trans iff.trans.
note#dual iff.sym.

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

note#cong iff.cong.

lemma imp_cong#cong if PQ: P ⟺ Q, RS: Q ⟹ R ⟺ S then (P ⟹ R) ⟺ (Q ⟹ S);
	apply iff_intro;
	- if PR, Q;
		note P: Q[fold PQ].
		note R: PR[OF P].
		by R[unfold RS[OF Q]].
	- if QS, P;
		note Q: P[unfold PQ].
		note S: QS[OF Q].
		by S[fold RS[OF Q]].
	.

lemma imp_cong_right#rule_cong if QR: Q ⟺ R then (P ⟹ Q) ⟺ (P ⟹ R);
	unfold QR.

interpret imp: iff.MetaCompatible (⟹);
	- if PQ: P ⟺ Q, RS: R ⟺ S then (P ⟹ R) ⟺ (Q ⟹ S);
		simp PQ RS.
	.

lemma all_cong#cong if PQ: ∀x. P.[x] ⟺ Q.[x] then (∀x. P.[x]) ⟺ (∀x. Q.[x]);
	apply iff_intro;
	- if ! ∀x. P.[x] then ∀x. Q.[x];
		by iff_elim1[OF PQ].
	- if ! ∀x. Q.[x] then ∀x. P.[x];
		by iff_elim2[OF PQ].
	.

note#rule_cong all_cong.

lemma imp_imp_iff: if !P then (P ⟹ Q) ⟺ Q;
	by iff_intro.

lemma imp_iff_iff: if !P then (P ⟺ Q) ⟺ Q;
	by iff_intro #elim iff_elim.

lemma imp_imp_commute: (P ⟹ Q ⟹ R) ⟺ (Q ⟹ P ⟹ R);
	by iff_intro.

lemma all_imp2_iff#simp (∀Q. (P ⟹ Q) ⟹ Q) ⟺ P;
	by iff_intro.

lemma imp3_iff: (((P ⟹ Q) ⟹ Q) ⟹ Q) ⟺ (P ⟹ Q);
	apply iff_intro[OF imp2_imp_imp];
	- if PQ: P ⟹ Q, PQQ: (P ⟹ Q) ⟹ Q then Q;
		by PQQ[OF PQ].
	.

lemma all_indep#simp (∀x. P) ⟺ P;
	by iff_intro.

lemma imp_all_iff: (P ⟹ ∀x. Q.[x]) ⟺ (∀x. P ⟹ Q.[x]);
	apply iff_intro;
	- if imp; by imp.
	- if imp; by imp.
	.

lemma imp_iff_iff1: if !P then (P ⟺ Q) ⟺ Q;
	by iff_intro #elim iff_elim.

extend True begin

	interpret imp: iff.MetaLeftNeutral (⟹) true;
		by imp_imp_iff.

	interpret imp: iff.MetaRightAbsorb (⟹) true;
		by iff_intro.

	interpret iff: iff.MetaCommNeutral (⟺) true;
		by iff_intro #elim iff_elim.

	note#simp imp.left_neutral imp.right_absorb iff.left_neutral iff.right_neutral.

	lemma iff_true: P ⟹ P ⟺ true.

end

extend False begin

	lemma false_iff: false ⟺ (∀P. P);
		by iff_intro.

	extend True begin
		lemma false_imp_iff#simp (false ⟹ P) ⟺ true;
			by iff_true.
	end

end

---
## Deriving Restricted Quantifiers via `(⟺)`
---

theory AllRel (⊏) :=
	fix (∀⊏).
	assume all_iff: (∀x ⊏ a. P.[x]) ⟺ (∀x. x ⊏ a ⟹ P.[x]).
begin

	interpret! Std.AllRel;
		- if all: ∀x. x ⊏ a ⟹ P.[x] then ∀x ⊏ a. P.[x];
			by all[fold all_iff].
		- for x if allIn: ∀y ⊏ a. P.[y], x: x ⊏ a then P.[x];
			by allIn[unfold all_iff, OF x].
		.
	lemma all_cong_strong:
		if a: ∀x. x ⊏ a ⟺ x ⊏ a', P: ∀x. x ⊏ a' ⟹ (P.[x] ⟺ P'.[x])
		then (∀x ⊏ a. P.[x]) ⟺ (∀x ⊏ a'. P'.[x]);
		unfold+ all_iff a P.

	lemma all_cong_weak:
		if P: ∀x. x ⊏ a ⟹ (P.[x] ⟺ P'.[x]) then (∀x ⊏ a. P.[x]) ⟺ (∀x ⊏ a. P'.[x]);
		unfold+ all_iff P.

	lemma imp_all_iff: (P ⟹ ∀x ⊏ a. Q.[x]) ⟺ (∀x ⊏ a. P ⟹ Q.[x]);
		by iff_intro #simp all_iff.

	lemma all_imp: ((∀x ⊏ a. P.[x]) ⟹ Q) ⟺ ((∀x. x ⊏ a ⟹ P.[x]) ⟹ Q);
		simp all_iff.

end

theory ExRel (⊏) :=
	fix (∃⊏).
	assume ex_iff_all: (∃x ⊏ a. P.[x]) ⟺ (∀Q. (∀x. x ⊏ a ⟹ P.[x] ⟹ Q) ⟹ Q).
begin

	interpret Std.ExRel;
		- for x if Px: P.[x], xa: x ⊏ a then ∃x ⊏ a. P.[x];
			unfold ex_iff_all;
			- for Q if all: ∀x. x ⊏ a ⟹ P.[x] ⟹ Q then Q;
				by all[OF xa Px].
			.
		- if ex: ∃x ⊏ a. P.[x], imp: ∀x. P.[x] ⟹ x ⊏ a ⟹ Q then Q;
			by ex[unfold ex_iff_all, OF imp[OF _ <]].
		.
	lemma ex_cong_strong:
		if a: ∀x. x ⊏ a ⟺ x ⊏ a', P: ∀x. x ⊏ a' ⟹ (P.[x] ⟺ P'.[x])
		then (∃x ⊏ a. P.[x]) ⟺ (∃x ⊏ a'. P'.[x]);
		unfold+ ex_iff_all;
		unfold a;
		unfold P;.

	lemma ex_cong_weak:
		if P: ∀x. x ⊏ a ⟹ (P.[x] ⟺ P'.[x]) then (∃x ⊏ a. P.[x]) ⟺ (∃x ⊏ a. P'.[x]);
		unfold+ ex_iff_all P.

	lemma ex_imp_iff#simp#rule ((∃x ⊏ a. P.[x]) ⟹ Q) ⟺ (∀x. x ⊏ a ⟹ P.[x] ⟹ Q);
		apply iff_intro;
		- if imp, x: x ⊏ a, Px: P.[x];
			apply imp ex_intro1[OF Px x].
		- if all, ex;
			apply ex_elim[OF ex];
			- for x if x, Px;
				apply all[OF Px x].
			.
		.

end

---
We can also formalize that the intro/elim formulations are equivalent to the iff ones.
---
theory NaiveAllRel :=
	import Std.AllRel.
begin

	interpret AllRel;
		- show all_iff: (∀x ⊏ a. P.[x]) ⟺ (∀x. x ⊏ a ⟹ P.[x]);
			apply iff_intro;
			- by #elim all_elim.
			by all_intro.
		.

end
