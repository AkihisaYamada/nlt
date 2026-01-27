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

namespace iff:

	-- We can think of meta-magmas with respect to ⟺
	interpret MetaMagmas (⟺).

	interpret MetaEquivalence (⟺);
		-; by iff_intro.
		-; by iff_intro #elim iff_elim.
		- if PQ: P ⟺ Q, QR: Q ⟺ R then P ⟺ R;
			apply iff_intro;
			-; by iff_elim1[OF QR] iff_elim1[OF PQ].
			-; by iff_elim2[OF PQ] iff_elim2[OF QR].
			.
		.
	--

end

note! iff.refl.

set rewrite iff_elim1 iff_elim2 iff.refl iff.trans.
set dual iff.sym.

context iff begin

	interpret MetaCompatible (⟺);
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

	interpret imp: MetaCompatible (⟹);
		- if PQ: P ⟺ Q, RS: R ⟺ S then (P ⟹ R) ⟺ (Q ⟹ S);
			apply iff_intro;
			- if PR: P ⟹ R, !Q then S;
				by iff_elim1[OF RS] PR iff_elim2[OF PQ].
			- if QS: Q ⟹ S, !P then R;
				by iff_elim2[OF RS] QS iff_elim1[OF PQ].
			.
		.

	lemma imp_cong: if PQ: P ⟺ Q, RS: Q ⟹ R ⟺ S then (P ⟹ R) ⟺ (Q ⟹ S);
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

	lemma all_cong: if PQ: ∀x. P.[x] ⟺ Q.[x] then (∀x. P.[x]) ⟺ (∀x. Q.[x]);
		apply iff_intro;
		- if ! ∀x. P.[x] then ∀x. Q.[x];
			by iff_elim1[OF PQ].
		- if ! ∀x. Q.[x] then ∀x. P.[x];
			by iff_elim2[OF PQ].
		.

end

note(cong) iff.cong iff.imp_cong iff.all_cong.

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

lemma imp_iff_iff1: if [P] then (P ⟺ Q) ⟺ Q;
	by iff_intro #elim iff_elim.
