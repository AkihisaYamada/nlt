import Base.
import Prop.

fix (⟺).

assume iff_type! P ∈ PROP ⟹ Q ∈ PROP ⟹ (P ⟺ Q) ∈ PROP.
assume iff_intro: (P ⟹ Q) ⟹ (Q ⟹ P) ⟹ P ∈ PROP ⟹ Q ∈ PROP ⟹ (P ⟺ Q).
assume iff_elim1: (P ⟺ Q) ⟹ P ⟹ P ∈ PROP ⟹ Q ∈ PROP ⟹ Q.
assume iff_elim2: (P ⟺ Q) ⟹ Q ⟹ P ∈ PROP ⟹ Q ∈ PROP ⟹ P.

begin

lemma iff_elim:
	if PQ: P ⟺ Q then ∀R. ((P ⟹ Q) ⟹ (Q ⟹ P) ⟹ R) ⟹ P ∈ PROP ⟹ Q ∈ PROP ⟹ R;
	for R if assm, !, !;
		apply assm;
		- by iff_elim1[OF PQ].
		- by iff_elim2[OF PQ].
		.
	.
ctxt.
interpret iff: Equivalence PROP (⟺);
ctxt.

	for P Q R if PQ: P ⟺ Q, QR: Q ⟺ R, !P ∈ PROP, !Q ∈ PROP, !R ∈ PROP then P ⟺ R;
		apply iff_intro;
		- by iff_elim1[OF QR] iff_elim1[OF PQ].
		by iff_elim2[OF PQ] iff_elim2[OF QR].
ctxt.
	by iff_intro #elim iff_elim.
ctxt.

note ! iff.refl.


lemma iff_imp: if PQ: P ⟺ Q, [P ∈ PROP, Q ∈ PROP] then P ⟹ Q;
	by iff_elim1[OF PQ].

lemma iff_imp_rev: if PQ: P ⟺ Q, [P ∈ PROP, Q ∈ PROP] then Q ⟹ P;
	by iff_elim2[OF PQ].

set rewrite iff_imp iff_imp_rev iff.refl iff.trans.
set dual iff.sym.

lemma iff_cong_imp: for P Q
	if PP': P ⟺ P', QQ': P' ⟹ Q ⟺ Q', [P ∈ PROP, P' ∈ PROP, Q ∈ PROP, Q' ∈ PROP]
	then (P ⟹ Q) ⟺ (P' ⟹ Q');
	apply iff_intro;
	- by #unfold QQ'[dual] PP'.
	- by #unfold QQ' PP'.
	.

lemma iff_cong_imp_weak#cong: for P Q
	if PP': P ⟺ P', QQ': Q ⟺ Q', [P ∈ PROP, Q ∈ PROP, P' ∈ PROP, Q' ∈ PROP]
	then (P ⟹ Q) ⟺ (P' ⟹ Q');
	apply iff_intro;
	- by #unfold QQ'[dual] PP'.
	- by #unfold QQ' PP'.
	.

lemma iff_cong_iff#cong: for P Q
	if PP': P ⟺ P', QQ': Q ⟺ Q', [P ∈ PROP, Q ∈ PROP, P' ∈ PROP, Q' ∈ PROP]
	then (P ⟺ Q) ⟺ (P' ⟺ Q');
	apply iff_intro;
	if PQ: P ⟺ Q;
		apply iff_intro;
		- by #unfold QQ'[dual] PQ[dual] PP'.
		- by #unfold PP'[dual] PQ QQ'.
		.
	if P'Q': P' ⟺ Q';
		apply iff_intro;
		- by #unfold QQ' P'Q'[dual] PP'[dual].
		- by #unfold PP' P'Q' QQ'[dual].
		.
	.

interpret iff: Magma prop (⟺).

lemma imp_imp_iff: if [P, P ∈ PROP, Q ∈ PROP] then (P ⟹ Q) ⟺ Q;
	by iff_intro.

lemma imp_iff_iff: if [P, P ∈ PROP, Q ∈ PROP] then (P ⟺ Q) ⟺ Q;
	by iff_intro #elim iff_elim1.

lemma imp3_iff: if [P ∈ PROP, Q ∈ PROP] then (((P ⟹ Q) ⟹ Q) ⟹ Q) ⟺ (P ⟹ Q);
	apply iff_intro[OF imp2_imp_imp];
	if PQ: P ⟹ Q, PQQ: (P ⟹ Q) ⟹ Q then Q;
		by PQQ[OF PQ].
	.
end

