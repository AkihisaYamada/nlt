fix (⟷).
import iff: Magma Prop (⟷).
assume iff_intro: if P ⟹ Q, Q ⟹ P, P : Prop, Q : Prop then P ⟷ Q.
assume iff_elim1: if P ⟷ Q, P, P : Prop, Q : Prop then Q.
assume iff_elim2: if P ⟷ Q, Q, P : Prop, Q : Prop then P.

import True, Imp.

begin

set simp (⟷).
set rule (⟷).

note#rewrite_imp iff_elim1[OF _ > _ _ ].
note#rewrite_rev iff_elim2[OF _ > _ _ ].
note! iff.closed.

instance iff: Magmas (⟷) (:).-- Magma notions wrt (⟷)

lemma iff_elim: if PQ: P ⟷ Q, imp: (P ⟹ Q) ⟹ (Q ⟹ P) ⟹ R, [P : Prop, Q : Prop] then R;
	by imp iff_elim1[OF PQ] iff_elim2[OF PQ].

-- We can think of meta-magmas with respect to ⟷
instance iff: Relation Prop (⟷).
instance iff: Equivalence Prop (⟷);
	- by iff_intro.
	- by iff_intro #elim iff_elim.
	- if PQ: P ⟷ Q, QR: Q ⟷ R, ... then P ⟷ R;
		apply iff_intro;
		- by iff_elim1[OF QR] iff_elim1[OF PQ].
		- by iff_elim2[OF PQ] iff_elim2[OF QR].
		.
	.
note#intro#refl iff.refl.
note#trans iff.trans.
note#dual iff.sym.

instance iff: iff.Compatible Prop (⟷);
	- if PQ: P ⟷ Q, RS: R ⟷ S, ... then (P ⟷ R) ⟷ (Q ⟷ S);
		apply iff_intro;
		- if PR: P ⟷ R then Q ⟷ S;
			.. ⟷ P; by PQ[dual].
			.. ⟷ R; by PR.
			by RS.
		- if QS: Q ⟷ S then P ⟷ R;
			.. ⟷ Q; by PQ.
			.. ⟷ S; by QS.
			by RS[dual].
		.
	.

note#cong iff.cong.

instance iff: iff.CommMagma (⟷);
	by iff_intro #elim iff_elim.

lemma imp_iff_iff1: if !P, [P : Prop, Q : Prop] then (P ⟷ Q) ⟷ Q;
	by iff_intro #elim iff_elim.

instance iff: iff.Neutral true;
	- if Q: Q ⟷ Q', [P : Prop, Q : Prop, Q' : Prop] then (P ⟷ Q) ⟷ (P ⟷ Q');
		simp Q.
	by iff_intro #elim iff_elim.

note#simp iff.left_neutral iff.right_neutral.

lemma iff_true: if !P, [P : Prop] then P ⟷ true.

lemma imp_cong#cong
	if PQ: P ⟷ Q, RS: Q ⟹ R ⟷ S, [P : Prop, Q : Prop, R : Prop, S : Prop]
	then (P ⟶ R) ⟷ (Q ⟶ S);
	apply iff_intro;
	- if PR; apply imp_intro;
		- if Q;
			fold RS[OF Q];
			apply PR[THEN imp_elim1];
			unfold PQ;
			by Q.
		.
	- if QS; apply imp_intro;
		- if P;
			unfold RS[OF P[unfold PQ]];
			apply QS[THEN imp_elim1];
			fold PQ;
			by P.
		.
	.

lemma imp_cong_right#rule_cong if QR: P ⟹ Q ⟷ R, [P : Prop, Q : Prop, R : Prop] then (P ⟶ Q) ⟷ (P ⟶ R);
	unfold QR.

instance IMP: iff.Compatible Prop (⟶);
	- if PQ: P ⟷ Q, RS: R ⟷ S, ... then (P ⟶ R) ⟷ (Q ⟶ S);
		simp PQ RS.
	.

note#cong IMP.cong.

lemma imp_imp_iff: if !P, [P : Prop, Q : Prop] then (P ⟶ Q) ⟷ Q;
	by iff_intro.

lemma imp_iff_iff: if !P, [P : Prop, Q : Prop] then (P ⟷ Q) ⟷ Q;
	by iff_intro #elim iff_elim.

lemma imp_imp_commute: if [P : Prop, Q : Prop, R : Prop] then (P ⟶ Q ⟶ R) ⟷ (Q ⟶ P ⟶ R);
	apply iff_intro;
	- if PQR; apply imp_intro;
		- if Q; apply imp_intro;
			- if P; apply PQR[THEN imp_elim1, OF P ! !, THEN imp_elim1, OF Q].
			.
		.
	- if QPR; apply imp_intro;
		- if P; apply imp_intro;
			- if Q; apply QPR[THEN imp_elim1, OF Q ! !, THEN imp_elim1, OF P].
			.
		.
	.

instance imp: iff.LeftNeutral Prop (⟶) true;
	by imp_imp_iff.

instance imp: iff.RightAbsorb Prop (⟶) true;
	by iff_intro.

note#simp imp.left_neutral imp.right_absorb.

extend AllRelStrict begin

	lemma all_cong:
		if PQ: ∀x. x ⊏ a ⟹ P.[x] ⟷ Q.[x],
		   [a : A, ∀x. x ⊏ a ⟹ P.[x] : Prop, ∀x. x ⊏ a ⟹ Q.[x] : Prop]
		then (∀x ⊏ a. P.[x]) ⟷ (∀x ⊏ a. Q.[x]);
		apply iff_intro;
		- if P;
			apply all_intro;
			- if ! x ⊏ a; fold PQ; by all_elim1[of x, OF P].
			.
		- if Q;
			apply all_intro;
			- if ! x ⊏ a; unfold PQ; by all_elim1[of x, OF Q].
			.
		.

end

extend ExRelStrict begin

	lemma ex_cong:
		if PQ: ∀x. x ⊏ a ⟹ P.[x] ⟷ Q.[x],
		   [a : A, ∀x. x ⊏ a ⟹ P.[x] : Prop, ∀x. x ⊏ a ⟹ Q.[x] : Prop]
		then (∃x ⊏ a. P.[x]) ⟷ (∃x ⊏ a. Q.[x]);
		apply iff_intro;
		- if P;
			apply ex_elim[OF P];
			- if ! P.[x], ...; apply ex_intro1[of x]; fold PQ.
			.
		- if Q;
			apply ex_elim[OF Q];
			- if ! Q.[x], ...; apply ex_intro1[of x]; unfold PQ.
			.
		.

end

extend Quantifiable begin

	instance AllRelStrict QTYPE (:) (∀:).
	instance ExRelStrict QTYPE (:) (∃:).

	note#cong#rule_cong all_cong ex_cong.

end
