---
# If-and-only-if
---
fix (⟺).

assume iff_intro: if P ⟹ Q, Q ⟹ P then P ⟺ Q.
assume iff_elim1: if P ⟺ Q, P then Q.
assume iff_elim2: if P ⟺ Q, Q then P.

begin

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
note! iff.refl.

set simp iff_elim1 iff_elim2 iff.refl iff.trans.
set rule iff_elim1 iff_elim2 iff.refl iff.trans.

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

lemma all_imp2_iff: (∀Q. (P ⟹ Q) ⟹ Q) ⟺ P;
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

---
## True
---
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


---
## Conjunction
---	
theory And :=
	fix (∧).
	assume and_iff: P ∧ Q ⟺ (∀R. (P ⟹ Q ⟹ R) ⟹ R).
begin

	interpret TypeFree.And;
		- for P Q if P: P, Q: Q then P ∧ Q;
			unfold and_iff;
			- if PQR: P ⟹ Q ⟹ R	then R;
				by PQR[OF P Q].
			.
		- if PQ: P ∧ Q then P;
			by PQ[unfold and_iff].
		- if PQ: P ∧ Q then Q;
			by PQ[unfold and_iff].
		.

	interpret and: iff.MetaCompatible (∧);
		- if P: P ⟺ P', Q: Q ⟺ Q' then P ∧ Q ⟺ P' ∧ Q';
			by iff_intro #simp P Q.
		.

	lemma and_cong1#cong if P: P ⟺ P', Q: P' ⟹ Q ⟺ Q' then P ∧ Q ⟺ P' ∧ Q';
		by iff_intro #simp P Q.

	interpret and: iff.MetaIdempotent (∧);
		by iff_intro.

	interpret and: iff.MetaCommSemigroup (∧);
		by iff_intro.

	lemma and_imp_iff_imp_imp#simp#rule (P ∧ Q ⟹ R) ⟺ (P ⟹ Q ⟹ R);
		by iff_intro.

	lemma imp_and_iff1#simp if P: P then P ∧ Q ⟺ Q;
		by iff_intro P.

	lemma imp_and_iff2#simp if Q: Q then P ∧ Q ⟺ P;
		by iff_intro Q.

	lemma and_iff: P ∧ Q ⟺ (∀R. (P ⟹ Q ⟹ R) ⟹ R);
		apply iff_intro;
		- simp imp_imp_iff.
		- if assm;
			apply assm.
		.

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
			- by and_elim1[OF ab].
			- by and_elim2[OF ab].
			.
		.

end

context True begin

	extend And begin

		interpret and: iff.MetaCommMonoid (∧) true;
			by iff_intro.

		note #simp and.left_neutral and.right_neutral.

	end

end

extend Not begin

	lemma not_cong#cong if PQ: P ⟺ Q then ¬P ⟺ ¬Q;
		apply iff_intro;
		by imp_imp_not_imp_not[OF iff_elim2[OF PQ]] imp_imp_not_imp_not[OF iff_elim1[OF PQ]].

	lemma imp_not_commute: (P ⟹ ¬Q) ⟺ (Q ⟹ ¬P);
		by iff_intro[OF imp_not_sym imp_not_sym].

	lemma nnnot_iff: ¬ ¬ ¬ P ⟺ ¬P;
		apply iff_intro[OF nnnot_imp_not nnot_intro].

	lemma nnot_imp_not_iff: (¬ ¬ P ⟹ ¬Q) ⟺ (P ⟹ ¬Q);
		unfold imp_not_commute;
		unfold nnnot_iff.

	lemma nnimp_not_iff: ¬ ¬ (P ⟹ ¬Q) ⟺ (P ⟹ ¬Q);
		apply iff_intro;
		- if nnimp: ¬ ¬ (P ⟹ ¬Q), P: P then ¬Q;
			by nnimp_imp_nnot[OF nnimp P, unfold nnnot_iff].
		by nnot_intro.

end

---
## Deriving Restricted Quantifiers via `(⟺)`
---

extend base: MetaRelation begin

	theory AllRel :=
		fix (∀⊏).
		assume all_iff: (∀x ⊏ a. P.[x]) ⟺ (∀x. x ⊏ a ⟹ P.[x]).
	begin

		interpret base.AllRel;
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

end

---
We can show the intro/elim formulation of `AllRel` is equivalent to the iff one.
---

context Std.MetaRelation begin--TODO: how elegantly could this be done?

	context AllRel begin

		extend Iff begin

			interpret MetaRelation.

			interpret? AllRel;
				- show all_iff: (∀x ⊏ a. P.[x]) ⟺ (∀x. x ⊏ a ⟹ P.[x]);
					apply iff_intro;
					- by #elim all_elim.
					by all_intro.
				.
		end

	end

end

